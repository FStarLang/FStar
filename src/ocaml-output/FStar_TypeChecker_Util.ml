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
                                        let uu____3519 =
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
                                          let uu____3532 =
                                            FStar_TypeChecker_Env.monad_leq
                                              env
                                              c1_ed.FStar_Syntax_Syntax.mname
                                              c2_ed.FStar_Syntax_Syntax.mname
                                             in
                                          match uu____3532 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____3545 =
                                                FStar_TypeChecker_Env.monad_leq
                                                  env
                                                  c2_ed.FStar_Syntax_Syntax.mname
                                                  c1_ed.FStar_Syntax_Syntax.mname
                                                 in
                                              (match uu____3545 with
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
                                        match uu____3519 with
                                        | (c12,uu____3577,uu____3578,c22,c2_ed)
                                            ->
                                            let uu____3581 =
                                              FStar_TypeChecker_Env.lift_to_layered_effect
                                                env c12
                                                c2_ed.FStar_Syntax_Syntax.mname
                                               in
                                            (match uu____3581 with
                                             | (c13,g_lift) ->
                                                 let uu____3592 =
                                                   let uu____3597 =
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                       c13
                                                      in
                                                   let uu____3598 =
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                       c22
                                                      in
                                                   (uu____3597, uu____3598)
                                                    in
                                                 (match uu____3592 with
                                                  | (ct1,ct2) ->
                                                      let uu____3605 =
                                                        let uu____3616 =
                                                          FStar_List.hd
                                                            ct1.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____3617 =
                                                          FStar_List.map
                                                            FStar_Pervasives_Native.fst
                                                            ct1.FStar_Syntax_Syntax.effect_args
                                                           in
                                                        (uu____3616,
                                                          (ct1.FStar_Syntax_Syntax.result_typ),
                                                          uu____3617)
                                                         in
                                                      (match uu____3605 with
                                                       | (u1,t1,is1) ->
                                                           let uu____3651 =
                                                             let uu____3662 =
                                                               FStar_List.hd
                                                                 ct2.FStar_Syntax_Syntax.comp_univs
                                                                in
                                                             let uu____3663 =
                                                               FStar_List.map
                                                                 FStar_Pervasives_Native.fst
                                                                 ct2.FStar_Syntax_Syntax.effect_args
                                                                in
                                                             (uu____3662,
                                                               (ct2.FStar_Syntax_Syntax.result_typ),
                                                               uu____3663)
                                                              in
                                                           (match uu____3651
                                                            with
                                                            | (u2,t2,is2) ->
                                                                let uu____3697
                                                                  =
                                                                  FStar_TypeChecker_Env.inst_tscheme_with
                                                                    c2_ed.FStar_Syntax_Syntax.bind_wp
                                                                    [u1; u2]
                                                                   in
                                                                (match uu____3697
                                                                 with
                                                                 | (uu____3706,bind_t)
                                                                    ->
                                                                    let uu____3708
                                                                    =
                                                                    let uu____3721
                                                                    =
                                                                    let uu____3722
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_t
                                                                     in
                                                                    uu____3722.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____3721
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____3759
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    FStar_All.pipe_right
                                                                    uu____3759
                                                                    (fun
                                                                    uu____3776
                                                                     ->
                                                                    match uu____3776
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let uu____3787
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    c3
                                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                                     in
                                                                    (bs1,
                                                                    uu____3787))
                                                                    | 
                                                                    uu____3788
                                                                    ->
                                                                    let uu____3789
                                                                    =
                                                                    let uu____3791
                                                                    =
                                                                    let uu____3793
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____3793
                                                                    " is not an arrow"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____3791
                                                                     in
                                                                    failwith
                                                                    uu____3789
                                                                     in
                                                                    (match uu____3708
                                                                    with
                                                                    | 
                                                                    (bind_bs,bind_ct)
                                                                    ->
                                                                    let uu____3831
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
                                                                    let uu____3958
                                                                    =
                                                                    let uu____3985
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2)))
                                                                    bs  in
                                                                    FStar_All.pipe_right
                                                                    uu____3985
                                                                    (fun
                                                                    uu____4070
                                                                     ->
                                                                    match uu____4070
                                                                    with
                                                                    | 
                                                                    (l1,l2)
                                                                    ->
                                                                    let uu____4151
                                                                    =
                                                                    FStar_List.hd
                                                                    l2  in
                                                                    let uu____4164
                                                                    =
                                                                    let uu____4171
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                    FStar_List.hd
                                                                    uu____4171
                                                                     in
                                                                    (l1,
                                                                    uu____4151,
                                                                    uu____4164))
                                                                     in
                                                                    (match uu____3958
                                                                    with
                                                                    | 
                                                                    (rest_bs,f_b,g_b)
                                                                    ->
                                                                    (a_b,
                                                                    b_b,
                                                                    rest_bs,
                                                                    f_b, g_b))
                                                                    | 
                                                                    uu____4329
                                                                    ->
                                                                    let uu____4338
                                                                    =
                                                                    let uu____4340
                                                                    =
                                                                    let uu____4342
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____4342
                                                                    " does not have enough binders"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "bind_t: "
                                                                    uu____4340
                                                                     in
                                                                    failwith
                                                                    uu____4338
                                                                     in
                                                                    (match uu____3831
                                                                    with
                                                                    | 
                                                                    (a_b,b_b,rest_bs,f_b,g_b)
                                                                    ->
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
                                                                    let uu____4581
                                                                    =
                                                                    let uu____4590
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env
                                                                    [a_b;
                                                                    b_b]  in
                                                                    (uu____4590,
                                                                    [],
                                                                    FStar_TypeChecker_Common.trivial_guard)
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____4636
                                                                     ->
                                                                    fun b2 
                                                                    ->
                                                                    match uu____4636
                                                                    with
                                                                    | 
                                                                    (env1,is_uvars,g)
                                                                    ->
                                                                    let uu____4667
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
                                                                    (match uu____4667
                                                                    with
                                                                    | 
                                                                    (t,uu____4696,g_t)
                                                                    ->
                                                                    let uu____4710
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env1 
                                                                    [b2]  in
                                                                    let uu____4723
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g g_t  in
                                                                    (uu____4710,
                                                                    (FStar_List.append
                                                                    is_uvars
                                                                    [t]),
                                                                    uu____4723)))
                                                                    uu____4581
                                                                    rest_bs
                                                                     in
                                                                    match uu____4572
                                                                    with
                                                                    | 
                                                                    (uu____4734,rest_bs_uvars,g)
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
                                                                    let uu____4783
                                                                    =
                                                                    let uu____4790
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4790,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4783)
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
                                                                    let uu____4823
                                                                    =
                                                                    let uu____4824
                                                                    =
                                                                    let uu____4827
                                                                    =
                                                                    let uu____4828
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4828.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4827
                                                                     in
                                                                    uu____4824.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4823
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____4839,uu____4840::is4)
                                                                    ->
                                                                    let uu____4882
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4882
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____4915
                                                                    ->
                                                                    let uu____4916
                                                                    =
                                                                    let uu____4918
                                                                    =
                                                                    let uu____4920
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                     in
                                                                    Prims.op_Hat
                                                                    uu____4920
                                                                    " is not a repr type"
                                                                     in
                                                                    Prims.op_Hat
                                                                    "Type of f in bind_t:"
                                                                    uu____4918
                                                                     in
                                                                    failwith
                                                                    uu____4916
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
                                                                    let uu____4943
                                                                    =
                                                                    let uu____4944
                                                                    =
                                                                    let uu____4947
                                                                    =
                                                                    let uu____4948
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4948.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4947
                                                                     in
                                                                    uu____4944.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4943
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____4981
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____4981
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let bs_subst
                                                                    =
                                                                    let uu____4991
                                                                    =
                                                                    let uu____4998
                                                                    =
                                                                    let uu____4999
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4999
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____5020
                                                                    =
                                                                    let uu____5023
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5023
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4998,
                                                                    uu____5020)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4991
                                                                     in
                                                                    let c4 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c3  in
                                                                    let uu____5037
                                                                    =
                                                                    let uu____5038
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c4)  in
                                                                    uu____5038.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5037
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5043,uu____5044::is4)
                                                                    ->
                                                                    let uu____5086
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is4
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5086
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
                                                                    uu____5181))))))))))
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
                                        (FStar_TypeChecker_Env.is_layered_effect
                                           env
                                           (FStar_Syntax_Util.comp_effect_name
                                              c1))
                                          ||
                                          (FStar_TypeChecker_Env.is_layered_effect
                                             env
                                             (FStar_Syntax_Util.comp_effect_name
                                                c2))
                                         in
                                      if uu____5609
                                      then mk_layered_bind c1 b c2
                                      else
                                        (let c1_typ =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c1
                                            in
                                         let uu____5619 =
                                           destruct_comp c1_typ  in
                                         match uu____5619 with
                                         | (u_res_t1,res_t1,uu____5632) ->
                                             let uu____5633 =
                                               (FStar_Option.isSome b) &&
                                                 (should_return env e1opt
                                                    lc11)
                                                in
                                             if uu____5633
                                             then
                                               let e1 =
                                                 FStar_Option.get e1opt  in
                                               let x = FStar_Option.get b  in
                                               let uu____5642 =
                                                 FStar_Syntax_Util.is_partial_return
                                                   c1
                                                  in
                                               (if uu____5642
                                                then
                                                  (debug1
                                                     (fun uu____5656  ->
                                                        let uu____5657 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5659 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case a): Substituting %s for %s"
                                                          uu____5657
                                                          uu____5659);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    mk_bind c1 b c21))
                                                else
                                                  (let uu____5667 =
                                                     ((FStar_Options.vcgen_optimize_bind_as_seq
                                                         ())
                                                        &&
                                                        (lcomp_has_trivial_postcondition
                                                           lc11))
                                                       &&
                                                       (let uu____5670 =
                                                          FStar_TypeChecker_Env.try_lookup_lid
                                                            env
                                                            FStar_Parser_Const.with_type_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____5670)
                                                      in
                                                   if uu____5667
                                                   then
                                                     let e1' =
                                                       let uu____5695 =
                                                         FStar_Options.vcgen_decorate_with_type
                                                           ()
                                                          in
                                                       if uu____5695
                                                       then
                                                         FStar_Syntax_Util.mk_with_type
                                                           u_res_t1 res_t1 e1
                                                       else e1  in
                                                     (debug1
                                                        (fun uu____5707  ->
                                                           let uu____5708 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1'
                                                              in
                                                           let uu____5710 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case b): Substituting %s for %s"
                                                             uu____5708
                                                             uu____5710);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1')] c2
                                                          in
                                                       mk_seq c1 b c21))
                                                   else
                                                     (debug1
                                                        (fun uu____5725  ->
                                                           let uu____5726 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1
                                                              in
                                                           let uu____5728 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case c): Adding equality %s = %s"
                                                             uu____5726
                                                             uu____5728);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1)] c2
                                                          in
                                                       let x_eq_e =
                                                         let uu____5735 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_Syntax_Util.mk_eq2
                                                           u_res_t1 res_t1 e1
                                                           uu____5735
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
      | uu____5753 -> g2
  
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
            (let uu____5777 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____5777)
           in
        let flags =
          if should_return1
          then
            let uu____5785 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____5785
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____5803 =
          let uu____5804 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5804 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____5817 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____5817
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____5825 =
                  let uu____5827 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____5827  in
                (if uu____5825
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___741_5836 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___741_5836.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___741_5836.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___741_5836.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____5837 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____5837, g_c)
                 else
                   (let uu____5840 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____5840, g_c)))
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
                   let uu____5851 =
                     let uu____5852 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____5852
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____5851
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____5855 =
                   let uu____5860 =
                     let uu____5861 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____5861
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____5860  in
                 match uu____5855 with
                 | (bind_c,g_bind) ->
                     let uu____5870 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____5871 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____5870, uu____5871))
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
            fun uu____5907  ->
              match uu____5907 with
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
                    let uu____5919 =
                      ((let uu____5923 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____5923) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____5919
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____5941 =
        let uu____5942 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____5942  in
      FStar_Syntax_Syntax.fvar uu____5941 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6012  ->
                 match uu____6012 with
                 | (uu____6026,eff_label,uu____6028,uu____6029) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6042 =
          let uu____6050 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6088  ->
                    match uu____6088 with
                    | (uu____6103,uu____6104,flags,uu____6106) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6123  ->
                                match uu___5_6123 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6126 -> false))))
             in
          if uu____6050
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6042 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6163 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6165 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6165
              then
                let uu____6172 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____6172, FStar_TypeChecker_Env.trivial_guard)
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6211 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6211 with
                   | (if_then_else1,uu____6221,uu____6222) ->
                       let uu____6223 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6224 =
                         let uu____6229 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6230 =
                           let uu____6231 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____6240 =
                             let uu____6251 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____6260 =
                               let uu____6271 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____6280 =
                                 let uu____6291 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____6291]  in
                               uu____6271 :: uu____6280  in
                             uu____6251 :: uu____6260  in
                           uu____6231 :: uu____6240  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6229 uu____6230
                          in
                       uu____6224 FStar_Pervasives_Native.None uu____6223
                    in
                 let default_case =
                   let post_k =
                     let uu____6344 =
                       let uu____6353 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6353]  in
                     let uu____6372 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6344 uu____6372  in
                   let kwp =
                     let uu____6378 =
                       let uu____6387 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6387]  in
                     let uu____6406 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6378 uu____6406  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6413 =
                       let uu____6414 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6414]  in
                     let uu____6433 =
                       let uu____6436 =
                         let uu____6443 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6443
                          in
                       let uu____6444 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6436 uu____6444  in
                     FStar_Syntax_Util.abs uu____6413 uu____6433
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
                   let uu____6468 =
                     should_not_inline_whole_match ||
                       (let uu____6471 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6471)
                      in
                   if uu____6468 then cthen true else cthen false  in
                 let uu____6478 =
                   FStar_List.fold_right
                     (fun uu____6524  ->
                        fun uu____6525  ->
                          match (uu____6524, uu____6525) with
                          | ((g,eff_label,uu____6567,cthen),(celse,g_comp))
                              ->
                              let uu____6601 =
                                let uu____6606 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____6606
                                 in
                              (match uu____6601 with
                               | (cthen1,gthen) ->
                                   let uu____6613 =
                                     lift_and_destruct env cthen1 celse  in
                                   (match uu____6613 with
                                    | ((md,uu____6643,uu____6644),(uu____6645,uu____6646,wp_then),
                                       (uu____6648,uu____6649,wp_else)) ->
                                        let uu____6669 =
                                          let uu____6670 =
                                            ifthenelse md res_t g wp_then
                                              wp_else
                                             in
                                          mk_comp md u_res_t res_t uu____6670
                                            []
                                           in
                                        let uu____6671 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_comp gthen
                                           in
                                        (uu____6669, uu____6671)))) lcases
                     (default_case, FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____6478 with
                 | (comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____6696::[] -> (comp, g_comp)
                      | uu____6739 ->
                          let comp1 =
                            FStar_TypeChecker_Env.comp_to_comp_typ env comp
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              comp1.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____6758 = destruct_comp comp1  in
                          (match uu____6758 with
                           | (uu____6769,uu____6770,wp) ->
                               let uu____6772 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   md.FStar_Syntax_Syntax.match_wps
                                  in
                               (match uu____6772 with
                                | (uu____6783,ite_wp,uu____6785) ->
                                    let wp1 =
                                      let uu____6789 =
                                        let uu____6794 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u_res_t] env md ite_wp
                                           in
                                        let uu____6795 =
                                          let uu____6796 =
                                            FStar_Syntax_Syntax.as_arg res_t
                                             in
                                          let uu____6805 =
                                            let uu____6816 =
                                              FStar_Syntax_Syntax.as_arg wp
                                               in
                                            [uu____6816]  in
                                          uu____6796 :: uu____6805  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____6794 uu____6795
                                         in
                                      uu____6789 FStar_Pervasives_Native.None
                                        wp.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6849 =
                                      mk_comp md u_res_t res_t wp1
                                        bind_cases_flags
                                       in
                                    (uu____6849, g_comp)))))
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
          let uu____6883 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6883 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____6899 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____6905 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____6899 uu____6905
              else
                (let uu____6914 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____6920 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____6914 uu____6920)
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
          let uu____6945 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____6945
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____6948 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____6948
        then u_res
        else
          (let is_total =
             let uu____6955 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____6955
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____6966 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____6966 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6969 =
                    let uu____6975 =
                      let uu____6977 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____6977
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____6975)
                     in
                  FStar_Errors.raise_error uu____6969
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
      let uu____7001 = destruct_comp ct  in
      match uu____7001 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7020 = FStar_TypeChecker_Env.get_range env  in
            let uu____7021 =
              let uu____7026 =
                let uu____7027 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7027
                 in
              let uu____7030 =
                let uu____7031 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7040 =
                  let uu____7051 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7051]  in
                uu____7031 :: uu____7040  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7026 uu____7030  in
            uu____7021 FStar_Pervasives_Native.None uu____7020  in
          let uu____7084 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7084)
  
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
               let uu____7125 =
                 let uu____7126 = FStar_Syntax_Subst.compress t2  in
                 uu____7126.FStar_Syntax_Syntax.n  in
               match uu____7125 with
               | FStar_Syntax_Syntax.Tm_type uu____7130 -> true
               | uu____7132 -> false  in
             let uu____7134 =
               let uu____7135 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____7135.FStar_Syntax_Syntax.n  in
             match uu____7134 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7143 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7153 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7153
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7156 =
                     let uu____7157 =
                       let uu____7158 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7158
                        in
                     (FStar_Pervasives_Native.None, uu____7157)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7156
                    in
                 let e1 =
                   let uu____7164 =
                     let uu____7169 =
                       let uu____7170 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7170]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7169  in
                   uu____7164 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7195 -> (e, lc))
  
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
          (let uu____7230 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7230
           then
             let uu____7233 = FStar_Syntax_Print.term_to_string e  in
             let uu____7235 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____7237 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7233 uu____7235 uu____7237
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7247 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____7247 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7272 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7298 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____7298, false)
             else
               (let uu____7308 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____7308, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7321) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____7333 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____7333
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___924_7349 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___924_7349.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___924_7349.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___924_7349.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____7356 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____7356 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____7372 =
                      let uu____7373 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____7373 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____7393 =
                            let uu____7395 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____7395 = FStar_Syntax_Util.Equal  in
                          if uu____7393
                          then
                            ((let uu____7402 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7402
                              then
                                let uu____7406 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____7408 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____7406 uu____7408
                              else ());
                             (let uu____7413 = set_result_typ1 c  in
                              (uu____7413, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____7420 ->
                                   true
                               | uu____7428 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____7437 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____7437
                                  in
                               let lc1 =
                                 let uu____7439 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____7440 =
                                   let uu____7441 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____7441)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____7439 uu____7440
                                  in
                               ((let uu____7445 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7445
                                 then
                                   let uu____7449 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____7451 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____7453 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____7455 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____7449 uu____7451 uu____7453
                                     uu____7455
                                 else ());
                                (let uu____7460 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____7460 with
                                 | (c1,g_lc) ->
                                     let uu____7471 = set_result_typ1 c1  in
                                     let uu____7472 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____7471, uu____7472)))
                             else
                               ((let uu____7476 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7476
                                 then
                                   let uu____7480 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____7482 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____7480 uu____7482
                                 else ());
                                (let uu____7487 = set_result_typ1 c  in
                                 (uu____7487, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___961_7491 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___961_7491.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___961_7491.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___961_7491.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____7501 =
                      let uu____7502 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____7502
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____7512 =
                           let uu____7513 = FStar_Syntax_Subst.compress f1
                              in
                           uu____7513.FStar_Syntax_Syntax.n  in
                         match uu____7512 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____7520,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____7522;
                                           FStar_Syntax_Syntax.vars =
                                             uu____7523;_},uu____7524)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___977_7550 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___977_7550.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___977_7550.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___977_7550.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____7551 ->
                             let uu____7552 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____7552 with
                              | (c,g_c) ->
                                  ((let uu____7564 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7564
                                    then
                                      let uu____7568 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____7570 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____7572 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____7574 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____7568 uu____7570 uu____7572
                                        uu____7574
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
                                        let uu____7587 =
                                          let uu____7592 =
                                            let uu____7593 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____7593]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____7592
                                           in
                                        uu____7587
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____7620 =
                                      let uu____7625 =
                                        FStar_All.pipe_left
                                          (fun _7646  ->
                                             FStar_Pervasives_Native.Some
                                               _7646)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____7647 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____7648 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____7649 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____7625
                                        uu____7647 e uu____7648 uu____7649
                                       in
                                    match uu____7620 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___995_7657 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___995_7657.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___995_7657.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____7659 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____7659
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____7662 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____7662 with
                                         | (c2,g_lc) ->
                                             ((let uu____7674 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____7674
                                               then
                                                 let uu____7678 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____7678
                                               else ());
                                              (let uu____7683 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____7683))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_7692  ->
                              match uu___6_7692 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____7695 -> []))
                       in
                    let lc1 =
                      let uu____7697 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____7697 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1011_7699 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1011_7699.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1011_7699.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1011_7699.FStar_TypeChecker_Common.implicits)
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
        let uu____7735 =
          let uu____7738 =
            let uu____7743 =
              let uu____7744 =
                let uu____7753 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7753  in
              [uu____7744]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7743  in
          uu____7738 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7735  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____7776 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7776
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7795 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7811 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7828 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7828
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7844)::(ens,uu____7846)::uu____7847 ->
                    let uu____7890 =
                      let uu____7893 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7893  in
                    let uu____7894 =
                      let uu____7895 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7895  in
                    (uu____7890, uu____7894)
                | uu____7898 ->
                    let uu____7909 =
                      let uu____7915 =
                        let uu____7917 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____7917
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____7915)
                       in
                    FStar_Errors.raise_error uu____7909
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____7937)::uu____7938 ->
                    let uu____7965 =
                      let uu____7970 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____7970
                       in
                    (match uu____7965 with
                     | (us_r,uu____8002) ->
                         let uu____8003 =
                           let uu____8008 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8008
                            in
                         (match uu____8003 with
                          | (us_e,uu____8040) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8043 =
                                  let uu____8044 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8044
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8043
                                  us_r
                                 in
                              let as_ens =
                                let uu____8046 =
                                  let uu____8047 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8047
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8046
                                  us_e
                                 in
                              let req =
                                let uu____8051 =
                                  let uu____8056 =
                                    let uu____8057 =
                                      let uu____8068 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8068]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8057
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8056
                                   in
                                uu____8051 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8108 =
                                  let uu____8113 =
                                    let uu____8114 =
                                      let uu____8125 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8125]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8114
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8113
                                   in
                                uu____8108 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8162 =
                                let uu____8165 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8165  in
                              let uu____8166 =
                                let uu____8167 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8167  in
                              (uu____8162, uu____8166)))
                | uu____8170 -> failwith "Impossible"))
  
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
      (let uu____8204 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8204
       then
         let uu____8209 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8211 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8209 uu____8211
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
        (let uu____8265 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8265
         then
           let uu____8270 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8272 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8270
             uu____8272
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8283 =
      let uu____8285 =
        let uu____8286 = FStar_Syntax_Subst.compress t  in
        uu____8286.FStar_Syntax_Syntax.n  in
      match uu____8285 with
      | FStar_Syntax_Syntax.Tm_app uu____8290 -> false
      | uu____8308 -> true  in
    if uu____8283
    then t
    else
      (let uu____8313 = FStar_Syntax_Util.head_and_args t  in
       match uu____8313 with
       | (head1,args) ->
           let uu____8356 =
             let uu____8358 =
               let uu____8359 = FStar_Syntax_Subst.compress head1  in
               uu____8359.FStar_Syntax_Syntax.n  in
             match uu____8358 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8364 -> false  in
           if uu____8356
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8396 ->
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
          ((let uu____8443 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____8443
            then
              let uu____8446 = FStar_Syntax_Print.term_to_string e  in
              let uu____8448 = FStar_Syntax_Print.term_to_string t  in
              let uu____8450 =
                let uu____8452 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____8452
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____8446 uu____8448 uu____8450
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____8465 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____8465 with
              | (formals,uu____8481) ->
                  let n_implicits =
                    let uu____8503 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____8581  ->
                              match uu____8581 with
                              | (uu____8589,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____8596 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____8596 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____8503 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____8721 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____8721 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____8735 =
                      let uu____8741 =
                        let uu____8743 = FStar_Util.string_of_int n_expected
                           in
                        let uu____8745 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____8747 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____8743 uu____8745 uu____8747
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____8741)
                       in
                    let uu____8751 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____8735 uu____8751
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_8769 =
              match uu___7_8769 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____8812 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____8812 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _8943,uu____8930) when
                           _8943 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____8976,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____8978))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9012 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9012 with
                            | (v1,uu____9053,g) ->
                                ((let uu____9068 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9068
                                  then
                                    let uu____9071 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9071
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9081 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9081 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9174 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9174))))
                       | (uu____9201,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9238 =
                             let uu____9251 =
                               let uu____9258 =
                                 let uu____9263 = FStar_Dyn.mkdyn env  in
                                 (uu____9263, tau)  in
                               FStar_Pervasives_Native.Some uu____9258  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9251
                              in
                           (match uu____9238 with
                            | (v1,uu____9296,g) ->
                                ((let uu____9311 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9311
                                  then
                                    let uu____9314 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9314
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9324 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9324 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9417 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9417))))
                       | (uu____9444,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____9492 =
                       let uu____9519 = inst_n_binders t1  in
                       aux [] uu____9519 bs1  in
                     (match uu____9492 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____9591) -> (e, torig, guard)
                           | (uu____9622,[]) when
                               let uu____9653 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____9653 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____9655 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____9683 ->
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
            | uu____9696 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9708 =
      let uu____9712 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9712
        (FStar_List.map
           (fun u  ->
              let uu____9724 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9724 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9708 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9752 = FStar_Util.set_is_empty x  in
      if uu____9752
      then []
      else
        (let s =
           let uu____9770 =
             let uu____9773 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9773  in
           FStar_All.pipe_right uu____9770 FStar_Util.set_elements  in
         (let uu____9789 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9789
          then
            let uu____9794 =
              let uu____9796 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9796  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9794
          else ());
         (let r =
            let uu____9805 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9805  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9844 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9844
                     then
                       let uu____9849 =
                         let uu____9851 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9851
                          in
                       let uu____9855 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9857 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9849 uu____9855 uu____9857
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
        let uu____9887 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9887 FStar_Util.set_elements  in
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
        | ([],uu____9926) -> generalized_univ_names
        | (uu____9933,[]) -> explicit_univ_names
        | uu____9940 ->
            let uu____9949 =
              let uu____9955 =
                let uu____9957 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9957
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9955)
               in
            FStar_Errors.raise_error uu____9949 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____9979 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____9979
       then
         let uu____9984 = FStar_Syntax_Print.term_to_string t  in
         let uu____9986 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____9984 uu____9986
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____9995 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____9995
        then
          let uu____10000 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10000
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10009 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10009
         then
           let uu____10014 = FStar_Syntax_Print.term_to_string t  in
           let uu____10016 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10014 uu____10016
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
        let uu____10100 =
          let uu____10102 =
            FStar_Util.for_all
              (fun uu____10116  ->
                 match uu____10116 with
                 | (uu____10126,uu____10127,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10102  in
        if uu____10100
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10179 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10179
              then
                let uu____10182 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10182
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10189 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10189
               then
                 let uu____10192 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10192
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10210 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10210 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10244 =
             match uu____10244 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10281 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10281
                   then
                     let uu____10286 =
                       let uu____10288 =
                         let uu____10292 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10292
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10288
                         (FStar_String.concat ", ")
                        in
                     let uu____10340 =
                       let uu____10342 =
                         let uu____10346 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10346
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10359 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10361 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10359
                                   uu____10361))
                          in
                       FStar_All.pipe_right uu____10342
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10286
                       uu____10340
                   else ());
                  (let univs2 =
                     let uu____10375 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10387 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10387) univs1
                       uu____10375
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10394 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10394
                    then
                      let uu____10399 =
                        let uu____10401 =
                          let uu____10405 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10405
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10401
                          (FStar_String.concat ", ")
                         in
                      let uu____10453 =
                        let uu____10455 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10469 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10471 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10469
                                    uu____10471))
                           in
                        FStar_All.pipe_right uu____10455
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10399 uu____10453
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10492 =
             let uu____10509 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10509  in
           match uu____10492 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10599 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10599
                 then ()
                 else
                   (let uu____10604 = lec_hd  in
                    match uu____10604 with
                    | (lb1,uu____10612,uu____10613) ->
                        let uu____10614 = lec2  in
                        (match uu____10614 with
                         | (lb2,uu____10622,uu____10623) ->
                             let msg =
                               let uu____10626 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10628 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10626 uu____10628
                                in
                             let uu____10631 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10631))
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
                 let uu____10699 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10699
                 then ()
                 else
                   (let uu____10704 = lec_hd  in
                    match uu____10704 with
                    | (lb1,uu____10712,uu____10713) ->
                        let uu____10714 = lec2  in
                        (match uu____10714 with
                         | (lb2,uu____10722,uu____10723) ->
                             let msg =
                               let uu____10726 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10728 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10726 uu____10728
                                in
                             let uu____10731 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10731))
                  in
               let lecs1 =
                 let uu____10742 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10795 = univs_and_uvars_of_lec this_lec  in
                        match uu____10795 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10742 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10900 = lec_hd  in
                   match uu____10900 with
                   | (lbname,e,c) ->
                       let uu____10910 =
                         let uu____10916 =
                           let uu____10918 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10920 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10922 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10918 uu____10920 uu____10922
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10916)
                          in
                       let uu____10926 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10910 uu____10926
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10945 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10945 with
                         | FStar_Pervasives_Native.Some uu____10954 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10962 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10966 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10966 with
                              | (bs,kres) ->
                                  ((let uu____11010 =
                                      let uu____11011 =
                                        let uu____11014 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11014
                                         in
                                      uu____11011.FStar_Syntax_Syntax.n  in
                                    match uu____11010 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11015
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11019 =
                                          let uu____11021 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11021  in
                                        if uu____11019
                                        then fail1 kres
                                        else ()
                                    | uu____11026 -> fail1 kres);
                                   (let a =
                                      let uu____11028 =
                                        let uu____11031 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11034  ->
                                             FStar_Pervasives_Native.Some
                                               _11034) uu____11031
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11028
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11042 ->
                                          let uu____11051 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11051
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
                      (fun uu____11154  ->
                         match uu____11154 with
                         | (lbname,e,c) ->
                             let uu____11200 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11261 ->
                                   let uu____11274 = (e, c)  in
                                   (match uu____11274 with
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
                                                (fun uu____11314  ->
                                                   match uu____11314 with
                                                   | (x,uu____11320) ->
                                                       let uu____11321 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11321)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11339 =
                                                let uu____11341 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11341
                                                 in
                                              if uu____11339
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
                                          let uu____11350 =
                                            let uu____11351 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11351.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11350 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11376 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11376 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11387 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11391 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11391, gen_tvars))
                                in
                             (match uu____11200 with
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
        (let uu____11538 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11538
         then
           let uu____11541 =
             let uu____11543 =
               FStar_List.map
                 (fun uu____11558  ->
                    match uu____11558 with
                    | (lb,uu____11567,uu____11568) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11543 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11541
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11594  ->
                match uu____11594 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11623 = gen env is_rec lecs  in
           match uu____11623 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11722  ->
                       match uu____11722 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11784 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11784
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11832  ->
                           match uu____11832 with
                           | (l,us,e,c,gvs) ->
                               let uu____11866 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11868 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11870 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11872 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11874 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11866 uu____11868 uu____11870
                                 uu____11872 uu____11874))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11919  ->
                match uu____11919 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11963 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11963, t, c, gvs)) univnames_lecs
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
              (let uu____12024 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12024 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12030 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12033  -> FStar_Pervasives_Native.Some _12033)
                     uu____12030)
             in
          let is_var e1 =
            let uu____12041 =
              let uu____12042 = FStar_Syntax_Subst.compress e1  in
              uu____12042.FStar_Syntax_Syntax.n  in
            match uu____12041 with
            | FStar_Syntax_Syntax.Tm_name uu____12046 -> true
            | uu____12048 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1467_12069 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1467_12069.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1467_12069.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12070 -> e2  in
          let env2 =
            let uu___1470_12072 = env1  in
            let uu____12073 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1470_12072.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1470_12072.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1470_12072.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1470_12072.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1470_12072.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1470_12072.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1470_12072.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1470_12072.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1470_12072.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1470_12072.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1470_12072.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1470_12072.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1470_12072.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1470_12072.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1470_12072.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1470_12072.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1470_12072.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12073;
              FStar_TypeChecker_Env.is_iface =
                (uu___1470_12072.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1470_12072.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1470_12072.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1470_12072.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1470_12072.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1470_12072.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1470_12072.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1470_12072.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1470_12072.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1470_12072.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1470_12072.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1470_12072.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1470_12072.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1470_12072.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1470_12072.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1470_12072.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1470_12072.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1470_12072.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1470_12072.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1470_12072.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1470_12072.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1470_12072.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1470_12072.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1470_12072.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1470_12072.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1470_12072.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12075 = check1 env2 t1 t2  in
          match uu____12075 with
          | FStar_Pervasives_Native.None  ->
              let uu____12082 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12088 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12082 uu____12088
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12095 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12095
                then
                  let uu____12100 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12100
                else ());
               (let uu____12106 = decorate e t2  in (uu____12106, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12134 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12134
         then
           let uu____12137 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12137
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12151 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____12151 with
         | (c,g_c) ->
             let uu____12163 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____12163
             then
               let uu____12171 =
                 let uu____12173 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____12173  in
               (uu____12171, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____12181 =
                    let uu____12182 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____12182
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____12181
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____12183 = check_trivial_precondition env c1  in
                match uu____12183 with
                | (ct,vc,g_pre) ->
                    ((let uu____12199 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____12199
                      then
                        let uu____12204 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____12204
                      else ());
                     (let uu____12209 =
                        let uu____12211 =
                          let uu____12212 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____12212  in
                        discharge uu____12211  in
                      let uu____12213 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____12209, uu____12213)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12247 =
        match uu___8_12247 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12257)::[] -> f fst1
        | uu____12282 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12294 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12294
          (fun _12295  -> FStar_TypeChecker_Common.NonTrivial _12295)
         in
      let op_or_e e =
        let uu____12306 =
          let uu____12307 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12307  in
        FStar_All.pipe_right uu____12306
          (fun _12310  -> FStar_TypeChecker_Common.NonTrivial _12310)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12317  -> FStar_TypeChecker_Common.NonTrivial _12317)
         in
      let op_or_t t =
        let uu____12328 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12328
          (fun _12331  -> FStar_TypeChecker_Common.NonTrivial _12331)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12338  -> FStar_TypeChecker_Common.NonTrivial _12338)
         in
      let short_op_ite uu___9_12344 =
        match uu___9_12344 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12354)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12381)::[] ->
            let uu____12422 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12422
              (fun _12423  -> FStar_TypeChecker_Common.NonTrivial _12423)
        | uu____12424 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12436 =
          let uu____12444 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12444)  in
        let uu____12452 =
          let uu____12462 =
            let uu____12470 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12470)  in
          let uu____12478 =
            let uu____12488 =
              let uu____12496 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12496)  in
            let uu____12504 =
              let uu____12514 =
                let uu____12522 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12522)  in
              let uu____12530 =
                let uu____12540 =
                  let uu____12548 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12548)  in
                [uu____12540; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12514 :: uu____12530  in
            uu____12488 :: uu____12504  in
          uu____12462 :: uu____12478  in
        uu____12436 :: uu____12452  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12610 =
            FStar_Util.find_map table
              (fun uu____12625  ->
                 match uu____12625 with
                 | (x,mk1) ->
                     let uu____12642 = FStar_Ident.lid_equals x lid  in
                     if uu____12642
                     then
                       let uu____12647 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12647
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12610 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12651 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12659 =
      let uu____12660 = FStar_Syntax_Util.un_uinst l  in
      uu____12660.FStar_Syntax_Syntax.n  in
    match uu____12659 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12665 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12701)::uu____12702 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12721 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12730,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12731))::uu____12732 -> bs
      | uu____12750 ->
          let uu____12751 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12751 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12755 =
                 let uu____12756 = FStar_Syntax_Subst.compress t  in
                 uu____12756.FStar_Syntax_Syntax.n  in
               (match uu____12755 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12760) ->
                    let uu____12781 =
                      FStar_Util.prefix_until
                        (fun uu___10_12821  ->
                           match uu___10_12821 with
                           | (uu____12829,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____12830)) ->
                               false
                           | uu____12835 -> true) bs'
                       in
                    (match uu____12781 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____12871,uu____12872) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12944,uu____12945) ->
                         let uu____13018 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13038  ->
                                   match uu____13038 with
                                   | (x,uu____13047) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13018
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13096  ->
                                     match uu____13096 with
                                     | (x,i) ->
                                         let uu____13115 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13115, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13126 -> bs))
  
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
            let uu____13155 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13155
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
          let uu____13186 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13186
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
        (let uu____13229 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13229
         then
           ((let uu____13234 = FStar_Ident.text_of_lid lident  in
             d uu____13234);
            (let uu____13236 = FStar_Ident.text_of_lid lident  in
             let uu____13238 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13236 uu____13238))
         else ());
        (let fv =
           let uu____13244 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13244
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
         let uu____13256 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1627_13258 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1627_13258.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1627_13258.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1627_13258.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1627_13258.FStar_Syntax_Syntax.sigattrs)
           }), uu____13256))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13276 =
        match uu___11_13276 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13279 -> false  in
      let reducibility uu___12_13287 =
        match uu___12_13287 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13294 -> false  in
      let assumption uu___13_13302 =
        match uu___13_13302 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13306 -> false  in
      let reification uu___14_13314 =
        match uu___14_13314 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13317 -> true
        | uu____13319 -> false  in
      let inferred uu___15_13327 =
        match uu___15_13327 with
        | FStar_Syntax_Syntax.Discriminator uu____13329 -> true
        | FStar_Syntax_Syntax.Projector uu____13331 -> true
        | FStar_Syntax_Syntax.RecordType uu____13337 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13347 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13360 -> false  in
      let has_eq uu___16_13368 =
        match uu___16_13368 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13372 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____13451 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13458 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____13469 =
        let uu____13471 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_13477  ->
                  match uu___17_13477 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____13480 -> false))
           in
        FStar_All.pipe_right uu____13471 Prims.op_Negation  in
      if uu____13469
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____13501 =
            let uu____13507 =
              let uu____13509 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____13509 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____13507)  in
          FStar_Errors.raise_error uu____13501 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____13527 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____13535 =
            let uu____13537 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____13537  in
          if uu____13535 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____13547),uu____13548) ->
              ((let uu____13560 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____13560
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____13569 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____13569
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13580 ->
              let uu____13589 =
                let uu____13591 =
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
                Prims.op_Negation uu____13591  in
              if uu____13589 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13601 ->
              let uu____13608 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13608 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13616 ->
              let uu____13623 =
                let uu____13625 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13625  in
              if uu____13623 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13635 ->
              let uu____13636 =
                let uu____13638 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13638  in
              if uu____13636 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13648 ->
              let uu____13649 =
                let uu____13651 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13651  in
              if uu____13649 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13661 ->
              let uu____13674 =
                let uu____13676 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13676  in
              if uu____13674 then err'1 () else ()
          | uu____13686 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____13709 =
          let uu____13714 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____13714
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____13709
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____13733 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____13733
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____13751 =
                          let uu____13752 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13752.FStar_Syntax_Syntax.n  in
                        match uu____13751 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____13758 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____13784 =
          let uu____13785 = FStar_Syntax_Subst.compress t1  in
          uu____13785.FStar_Syntax_Syntax.n  in
        match uu____13784 with
        | FStar_Syntax_Syntax.Tm_type uu____13789 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____13792 ->
            let uu____13807 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13807 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____13840 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____13840
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____13846;
               FStar_Syntax_Syntax.index = uu____13847;
               FStar_Syntax_Syntax.sort = t2;_},uu____13849)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13858,uu____13859) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____13901::[]) ->
            let uu____13940 =
              let uu____13941 = FStar_Syntax_Util.un_uinst head1  in
              uu____13941.FStar_Syntax_Syntax.n  in
            (match uu____13940 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____13946 -> false)
        | uu____13948 -> false
      
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
        (let uu____13958 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____13958
         then
           let uu____13963 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____13963
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
                  let uu____14024 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14024 r  in
                let uu____14034 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14034 with
                | (uu____14043,signature) ->
                    let uu____14045 =
                      let uu____14046 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14046.FStar_Syntax_Syntax.n  in
                    (match uu____14045 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14054) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14102 =
                                FStar_List.fold_left
                                  (fun uu____14141  ->
                                     fun uu____14142  ->
                                       match (uu____14141, uu____14142) with
                                       | ((is,g,substs),(b,uu____14189)) ->
                                           let uu____14218 =
                                             let uu____14231 =
                                               FStar_Syntax_Subst.subst
                                                 substs
                                                 b.FStar_Syntax_Syntax.sort
                                                in
                                             new_implicit_var "" r env
                                               uu____14231
                                              in
                                           (match uu____14218 with
                                            | (t,uu____14244,g_t) ->
                                                let uu____14258 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g_t
                                                   in
                                                ((FStar_List.append is [t]),
                                                  uu____14258,
                                                  (FStar_List.append substs
                                                     [FStar_Syntax_Syntax.NT
                                                        (b, t)]))))
                                  ([], FStar_TypeChecker_Env.trivial_guard,
                                    [FStar_Syntax_Syntax.NT
                                       ((FStar_Pervasives_Native.fst a),
                                         a_tm)]) bs2
                                 in
                              (match uu____14102 with
                               | (is,g,uu____14279) ->
                                   let repr =
                                     let uu____14289 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14289
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14298 =
                                     let uu____14299 =
                                       let uu____14304 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14304
                                        in
                                     uu____14299 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14298, g))
                          | uu____14313 -> fail1 signature)
                     | uu____14314 -> fail1 signature)
  
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
        let uu____14362 = FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]
           in
        match uu____14362 with
        | (uu____14367,sig_tm) ->
            let uu____14369 =
              let uu____14370 = FStar_Syntax_Subst.compress sig_tm  in
              uu____14370.FStar_Syntax_Syntax.n  in
            (match uu____14369 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14374) ->
                 let bs1 = FStar_Syntax_Subst.open_binders bs  in
                 (match bs1 with
                  | (a',uu____14397)::bs2 ->
                      FStar_All.pipe_right bs2
                        (FStar_Syntax_Subst.subst_binders
                           [FStar_Syntax_Syntax.NT (a', a_tm)])
                  | uu____14419 -> failwith "Impossible!")
             | uu____14421 -> failwith "Impossible")
  