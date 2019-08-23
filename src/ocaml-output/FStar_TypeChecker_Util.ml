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
                                        (let uu____3512 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other
                                                "LayeredEffects")
                                            in
                                         if uu____3512
                                         then
                                           let uu____3517 =
                                             FStar_Syntax_Print.comp_to_string
                                               c11
                                              in
                                           let uu____3519 =
                                             FStar_Syntax_Print.comp_to_string
                                               c21
                                              in
                                           FStar_Util.print2
                                             "Binding c1:%s and c2:%s {\n"
                                             uu____3517 uu____3519
                                         else ());
                                        (let ct1 =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c11
                                            in
                                         let ct2 =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c21
                                            in
                                         let uu____3526 =
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
                                           let uu____3537 =
                                             FStar_TypeChecker_Env.monad_leq
                                               env
                                               c1_ed.FStar_Syntax_Syntax.mname
                                               c2_ed.FStar_Syntax_Syntax.mname
                                              in
                                           match uu____3537 with
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3548 =
                                                 FStar_TypeChecker_Env.monad_leq
                                                   env
                                                   c2_ed.FStar_Syntax_Syntax.mname
                                                   c1_ed.FStar_Syntax_Syntax.mname
                                                  in
                                               (match uu____3548 with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    let uu____3559 =
                                                      let uu____3565 =
                                                        FStar_Util.format2
                                                          "Effects %s and %s cannot be composed"
                                                          (c1_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                          (c2_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                         in
                                                      (FStar_Errors.Fatal_EffectsCannotBeComposed,
                                                        uu____3565)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3559 r1
                                                | FStar_Pervasives_Native.Some
                                                    uu____3577 ->
                                                    let uu____3578 =
                                                      let uu____3583 =
                                                        let uu____3588 =
                                                          FStar_Syntax_Syntax.mk_Comp
                                                            ct2
                                                           in
                                                        FStar_TypeChecker_Env.lift_to_layered_effect
                                                          env uu____3588
                                                          c1_ed.FStar_Syntax_Syntax.mname
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3583
                                                        (fun uu____3601  ->
                                                           match uu____3601
                                                           with
                                                           | (c,g) ->
                                                               let uu____3612
                                                                 =
                                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                                   c
                                                                  in
                                                               (uu____3612,
                                                                 g))
                                                       in
                                                    (match uu____3578 with
                                                     | (ct21,g_lift) ->
                                                         (ct1, ct21, c1_ed,
                                                           g_lift)))
                                           | FStar_Pervasives_Native.Some
                                               uu____3623 ->
                                               let uu____3624 =
                                                 let uu____3629 =
                                                   let uu____3634 =
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       ct1
                                                      in
                                                   FStar_TypeChecker_Env.lift_to_layered_effect
                                                     env uu____3634
                                                     c2_ed.FStar_Syntax_Syntax.mname
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3629
                                                   (fun uu____3647  ->
                                                      match uu____3647 with
                                                      | (c,g) ->
                                                          let uu____3658 =
                                                            FStar_Syntax_Util.comp_to_comp_typ
                                                              c
                                                             in
                                                          (uu____3658, g))
                                                  in
                                               (match uu____3624 with
                                                | (ct11,g_lift) ->
                                                    (ct11, ct2, c2_ed,
                                                      g_lift))
                                            in
                                         match uu____3526 with
                                         | (ct11,ct21,ed,g_lift) ->
                                             ((let uu____3678 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____3678
                                               then
                                                 let uu____3683 =
                                                   let uu____3685 =
                                                     FStar_All.pipe_right
                                                       ct11
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3685
                                                     FStar_Syntax_Print.comp_to_string
                                                    in
                                                 let uu____3687 =
                                                   let uu____3689 =
                                                     FStar_All.pipe_right
                                                       ct21
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3689
                                                     FStar_Syntax_Print.comp_to_string
                                                    in
                                                 FStar_Util.print2
                                                   "After lifting, ct1: %s and ct2: %s\n"
                                                   uu____3683 uu____3687
                                               else ());
                                              (let uu____3694 =
                                                 let uu____3705 =
                                                   FStar_List.hd
                                                     ct11.FStar_Syntax_Syntax.comp_univs
                                                    in
                                                 let uu____3706 =
                                                   FStar_List.map
                                                     FStar_Pervasives_Native.fst
                                                     ct11.FStar_Syntax_Syntax.effect_args
                                                    in
                                                 (uu____3705,
                                                   (ct11.FStar_Syntax_Syntax.result_typ),
                                                   uu____3706)
                                                  in
                                               match uu____3694 with
                                               | (u1,t1,is1) ->
                                                   let uu____3740 =
                                                     let uu____3751 =
                                                       FStar_List.hd
                                                         ct21.FStar_Syntax_Syntax.comp_univs
                                                        in
                                                     let uu____3752 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         ct21.FStar_Syntax_Syntax.effect_args
                                                        in
                                                     (uu____3751,
                                                       (ct21.FStar_Syntax_Syntax.result_typ),
                                                       uu____3752)
                                                      in
                                                   (match uu____3740 with
                                                    | (u2,t2,is2) ->
                                                        let uu____3786 =
                                                          FStar_TypeChecker_Env.inst_tscheme_with
                                                            ed.FStar_Syntax_Syntax.bind_wp
                                                            [u1; u2]
                                                           in
                                                        (match uu____3786
                                                         with
                                                         | (uu____3795,bind_t)
                                                             ->
                                                             let bind_t_shape_error
                                                               s =
                                                               let uu____3810
                                                                 =
                                                                 let uu____3812
                                                                   =
                                                                   FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind %s does not have proper shape (reason:%s)"
                                                                   uu____3812
                                                                   s
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____3810)
                                                                in
                                                             let uu____3816 =
                                                               let uu____3861
                                                                 =
                                                                 let uu____3862
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    bind_t
                                                                    in
                                                                 uu____3862.FStar_Syntax_Syntax.n
                                                                  in
                                                               match uu____3861
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c)
                                                                   when
                                                                   (FStar_List.length
                                                                    bs) >=
                                                                    (Prims.of_int (4))
                                                                   ->
                                                                   let uu____3938
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____3938
                                                                    with
                                                                    | 
                                                                    (a_b::b_b::bs1,c3)
                                                                    ->
                                                                    let uu____4023
                                                                    =
                                                                    let uu____4050
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs1) -
                                                                    (Prims.of_int (2)))
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4050
                                                                    (fun
                                                                    uu____4135
                                                                     ->
                                                                    match uu____4135
                                                                    with
                                                                    | 
                                                                    (l1,l2)
                                                                    ->
                                                                    let uu____4216
                                                                    =
                                                                    FStar_List.hd
                                                                    l2  in
                                                                    let uu____4229
                                                                    =
                                                                    let uu____4236
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                    FStar_List.hd
                                                                    uu____4236
                                                                     in
                                                                    (l1,
                                                                    uu____4216,
                                                                    uu____4229))
                                                                     in
                                                                    (match uu____4023
                                                                    with
                                                                    | 
                                                                    (rest_bs,f_b,g_b)
                                                                    ->
                                                                    let uu____4364
                                                                    =
                                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                                    c3  in
                                                                    (a_b,
                                                                    b_b,
                                                                    rest_bs,
                                                                    f_b, g_b,
                                                                    uu____4364)))
                                                               | uu____4397
                                                                   ->
                                                                   let uu____4398
                                                                    =
                                                                    bind_t_shape_error
                                                                    "Either not an arrow or not enough binders"
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____4398
                                                                    r1
                                                                in
                                                             (match uu____3816
                                                              with
                                                              | (a_b,b_b,rest_bs,f_b,g_b,bind_ct)
                                                                  ->
                                                                  let uu____4523
                                                                    =
                                                                    let uu____4532
                                                                    =
                                                                    let uu____4543
                                                                    =
                                                                    let uu____4554
                                                                    =
                                                                    let uu____4557
                                                                    =
                                                                    let uu____4558
                                                                    =
                                                                    let uu____4565
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    a_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4565,
                                                                    t1)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4558
                                                                     in
                                                                    let uu____4576
                                                                    =
                                                                    let uu____4579
                                                                    =
                                                                    let uu____4580
                                                                    =
                                                                    let uu____4587
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4587,
                                                                    t2)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4580
                                                                     in
                                                                    [uu____4579]
                                                                     in
                                                                    uu____4557
                                                                    ::
                                                                    uu____4576
                                                                     in
                                                                    (uu____4554,
                                                                    [],
                                                                    FStar_TypeChecker_Common.trivial_guard)
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____4632
                                                                     ->
                                                                    fun b2 
                                                                    ->
                                                                    match uu____4632
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
                                                                    let reason1
                                                                    =
                                                                    let uu____4676
                                                                    =
                                                                    FStar_Syntax_Print.binder_to_string
                                                                    b2  in
                                                                    let uu____4678
                                                                    =
                                                                    FStar_Range.string_of_range
                                                                    r1  in
                                                                    FStar_Util.format3
                                                                    "implicit var for binder %s of %s:bind at %s"
                                                                    uu____4676
                                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                    uu____4678
                                                                     in
                                                                    let uu____4681
                                                                    =
                                                                    FStar_TypeChecker_Env.new_implicit_var_aux
                                                                    reason1
                                                                    r1 env
                                                                    sort
                                                                    FStar_Syntax_Syntax.Strict
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (match uu____4681
                                                                    with
                                                                    | 
                                                                    (t,uu____4709,g_t)
                                                                    ->
                                                                    ((
                                                                    let uu____4724
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "LayeredEffects")
                                                                     in
                                                                    if
                                                                    uu____4724
                                                                    then
                                                                    let uu____4729
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    let uu____4731
                                                                    =
                                                                    FStar_Syntax_Print.binder_to_string
                                                                    b2  in
                                                                    FStar_Util.print2
                                                                    "mk_layered_bind: introducing uvar : %s for binder %s of bind\n"
                                                                    uu____4729
                                                                    uu____4731
                                                                    else ());
                                                                    (let uu____4736
                                                                    =
                                                                    let uu____4739
                                                                    =
                                                                    let uu____4742
                                                                    =
                                                                    let uu____4743
                                                                    =
                                                                    let uu____4750
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4750,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4743
                                                                     in
                                                                    [uu____4742]
                                                                     in
                                                                    FStar_List.append
                                                                    substs
                                                                    uu____4739
                                                                     in
                                                                    let uu____4761
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g g_t  in
                                                                    (uu____4736,
                                                                    (FStar_List.append
                                                                    is_uvars
                                                                    [t]),
                                                                    uu____4761)))))
                                                                    uu____4543
                                                                    rest_bs
                                                                     in
                                                                    match uu____4532
                                                                    with
                                                                    | 
                                                                    (uu____4774,rest_bs_uvars,g)
                                                                    ->
                                                                    (rest_bs_uvars,
                                                                    g)  in
                                                                  (match uu____4523
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
                                                                    let uu____4827
                                                                    =
                                                                    let uu____4834
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4834,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4827)
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
                                                                    let uu____4865
                                                                    =
                                                                    let uu____4866
                                                                    =
                                                                    let uu____4869
                                                                    =
                                                                    let uu____4870
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4870.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4869
                                                                     in
                                                                    uu____4866.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4865
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____4881,uu____4882::is)
                                                                    ->
                                                                    let uu____4924
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4924
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____4957
                                                                    ->
                                                                    let uu____4958
                                                                    =
                                                                    bind_t_shape_error
                                                                    "f's type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____4958
                                                                    r1  in
                                                                    FStar_List.fold_left2
                                                                    (fun g 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun f_i1 
                                                                    ->
                                                                    let uu____4974
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4974)
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
                                                                    let uu____4993
                                                                    =
                                                                    let uu____4994
                                                                    =
                                                                    let uu____4997
                                                                    =
                                                                    let uu____4998
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4998.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4997
                                                                     in
                                                                    uu____4994.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4993
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5031
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5031
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let bs_subst
                                                                    =
                                                                    let uu____5041
                                                                    =
                                                                    let uu____5048
                                                                    =
                                                                    let uu____5049
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____5049
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____5070
                                                                    =
                                                                    let uu____5073
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5073
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____5048,
                                                                    uu____5070)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____5041
                                                                     in
                                                                    let c4 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c3  in
                                                                    let uu____5087
                                                                    =
                                                                    let uu____5088
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c4)  in
                                                                    uu____5088.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5087
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5093,uu____5094::is)
                                                                    ->
                                                                    let uu____5136
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5136
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5169
                                                                    ->
                                                                    let uu____5170
                                                                    =
                                                                    bind_t_shape_error
                                                                    "g's type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5170
                                                                    r1))
                                                                    | 
                                                                    uu____5179
                                                                    ->
                                                                    let uu____5180
                                                                    =
                                                                    bind_t_shape_error
                                                                    "g's type is not an arrow"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5180
                                                                    r1  in
                                                                    let env_g
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [x_a]  in
                                                                    let uu____5202
                                                                    =
                                                                    FStar_List.fold_left2
                                                                    (fun g 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun g_i1 
                                                                    ->
                                                                    let uu____5210
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5210)
                                                                    FStar_TypeChecker_Env.trivial_guard
                                                                    is2
                                                                    g_sort_is
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5202
                                                                    (FStar_TypeChecker_Env.close_guard
                                                                    env 
                                                                    [x_a])
                                                                     in
                                                                    let is =
                                                                    let uu____5226
                                                                    =
                                                                    let uu____5227
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_ct.FStar_Syntax_Syntax.result_typ
                                                                     in
                                                                    uu____5227.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5226
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5232,uu____5233::is)
                                                                    ->
                                                                    let uu____5275
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5275
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5308
                                                                    ->
                                                                    let uu____5309
                                                                    =
                                                                    bind_t_shape_error
                                                                    "return type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5309
                                                                    r1  in
                                                                    let c =
                                                                    let uu____5319
                                                                    =
                                                                    let uu____5320
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
                                                                    uu____5320;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu____5319
                                                                     in
                                                                    ((
                                                                    let uu____5340
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "LayeredEffects")
                                                                     in
                                                                    if
                                                                    uu____5340
                                                                    then
                                                                    let uu____5345
                                                                    =
                                                                    FStar_Syntax_Print.comp_to_string
                                                                    c  in
                                                                    FStar_Util.print1
                                                                    "} c after bind: %s\n"
                                                                    uu____5345
                                                                    else ());
                                                                    (let uu____5350
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
                                                                    uu____5350))))))))))
                                         in
                                      let mk_bind c11 b1 c21 =
                                        let uu____5375 =
                                          lift_and_destruct env c11 c21  in
                                        match uu____5375 with
                                        | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2))
                                            ->
                                            let bs =
                                              match b1 with
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____5432 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      t1
                                                     in
                                                  [uu____5432]
                                              | FStar_Pervasives_Native.Some
                                                  x ->
                                                  let uu____5452 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____5452]
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
                                              let uu____5499 =
                                                FStar_Syntax_Syntax.as_arg
                                                  r11
                                                 in
                                              let uu____5508 =
                                                let uu____5519 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1
                                                   in
                                                let uu____5528 =
                                                  let uu____5539 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t2
                                                     in
                                                  let uu____5548 =
                                                    let uu____5559 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp1
                                                       in
                                                    let uu____5568 =
                                                      let uu____5579 =
                                                        let uu____5588 =
                                                          mk_lam wp2  in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____5588
                                                         in
                                                      [uu____5579]  in
                                                    uu____5559 :: uu____5568
                                                     in
                                                  uu____5539 :: uu____5548
                                                   in
                                                uu____5519 :: uu____5528  in
                                              uu____5499 :: uu____5508  in
                                            let wp =
                                              let uu____5640 =
                                                let uu____5645 =
                                                  FStar_TypeChecker_Env.inst_effect_fun_with
                                                    [u_t1; u_t2] env md
                                                    md.FStar_Syntax_Syntax.bind_wp
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5645 wp_args
                                                 in
                                              uu____5640
                                                FStar_Pervasives_Native.None
                                                t2.FStar_Syntax_Syntax.pos
                                               in
                                            let uu____5646 =
                                              mk_comp md u_t2 t2 wp
                                                bind_flags
                                               in
                                            let uu____5647 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_c1 g_c2
                                               in
                                            (uu____5646, uu____5647)
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
                                        let uu____5674 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5674 with
                                        | (m,uu____5686,lift2) ->
                                            let c23 =
                                              let uu____5689 =
                                                lift_comp c22 m lift2  in
                                              FStar_Syntax_Syntax.mk_Comp
                                                uu____5689
                                               in
                                            let uu____5690 =
                                              destruct_comp c12  in
                                            (match uu____5690 with
                                             | (u1,t1,wp1) ->
                                                 let md_pure_or_ghost =
                                                   FStar_TypeChecker_Env.get_effect_decl
                                                     env
                                                     c12.FStar_Syntax_Syntax.effect_name
                                                    in
                                                 let vc1 =
                                                   let uu____5708 =
                                                     let uu____5713 =
                                                       let uu____5714 =
                                                         FStar_All.pipe_right
                                                           md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                           FStar_Util.must
                                                          in
                                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                                         [u1] env
                                                         md_pure_or_ghost
                                                         uu____5714
                                                        in
                                                     let uu____5717 =
                                                       let uu____5718 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           t1
                                                          in
                                                       let uu____5727 =
                                                         let uu____5738 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             wp1
                                                            in
                                                         [uu____5738]  in
                                                       uu____5718 ::
                                                         uu____5727
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____5713 uu____5717
                                                      in
                                                   uu____5708
                                                     FStar_Pervasives_Native.None
                                                     r1
                                                    in
                                                 let uu____5771 =
                                                   strengthen_comp env
                                                     FStar_Pervasives_Native.None
                                                     c23 vc1 bind_flags
                                                    in
                                                 let uu____5776 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 g_c2
                                                    in
                                                 (uu____5771, uu____5776))
                                         in
                                      let uu____5777 =
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
                                      if uu____5777
                                      then mk_layered_bind c1 b c2
                                      else
                                        (let c1_typ =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c1
                                            in
                                         let uu____5789 =
                                           destruct_comp c1_typ  in
                                         match uu____5789 with
                                         | (u_res_t1,res_t1,uu____5802) ->
                                             let uu____5803 =
                                               (FStar_Option.isSome b) &&
                                                 (should_return env e1opt
                                                    lc11)
                                                in
                                             if uu____5803
                                             then
                                               let e1 =
                                                 FStar_Option.get e1opt  in
                                               let x = FStar_Option.get b  in
                                               let uu____5812 =
                                                 FStar_Syntax_Util.is_partial_return
                                                   c1
                                                  in
                                               (if uu____5812
                                                then
                                                  (debug1
                                                     (fun uu____5826  ->
                                                        let uu____5827 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5829 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case a): Substituting %s for %s"
                                                          uu____5827
                                                          uu____5829);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    mk_bind c1 b c21))
                                                else
                                                  (let uu____5837 =
                                                     ((FStar_Options.vcgen_optimize_bind_as_seq
                                                         ())
                                                        &&
                                                        (lcomp_has_trivial_postcondition
                                                           lc11))
                                                       &&
                                                       (let uu____5840 =
                                                          FStar_TypeChecker_Env.try_lookup_lid
                                                            env
                                                            FStar_Parser_Const.with_type_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____5840)
                                                      in
                                                   if uu____5837
                                                   then
                                                     let e1' =
                                                       let uu____5865 =
                                                         FStar_Options.vcgen_decorate_with_type
                                                           ()
                                                          in
                                                       if uu____5865
                                                       then
                                                         FStar_Syntax_Util.mk_with_type
                                                           u_res_t1 res_t1 e1
                                                       else e1  in
                                                     (debug1
                                                        (fun uu____5877  ->
                                                           let uu____5878 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1'
                                                              in
                                                           let uu____5880 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case b): Substituting %s for %s"
                                                             uu____5878
                                                             uu____5880);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1')] c2
                                                          in
                                                       mk_seq c1 b c21))
                                                   else
                                                     (debug1
                                                        (fun uu____5895  ->
                                                           let uu____5896 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1
                                                              in
                                                           let uu____5898 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case c): Adding equality %s = %s"
                                                             uu____5896
                                                             uu____5898);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1)] c2
                                                          in
                                                       let x_eq_e =
                                                         let uu____5905 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_Syntax_Util.mk_eq2
                                                           u_res_t1 res_t1 e1
                                                           uu____5905
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
      | uu____5923 -> g2
  
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
            (let uu____5947 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____5947)
           in
        let flags =
          if should_return1
          then
            let uu____5955 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____5955
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____5973 =
          let uu____5974 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5974 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____5987 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____5987
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____5995 =
                  let uu____5997 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____5997  in
                (if uu____5995
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___757_6006 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___757_6006.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___757_6006.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___757_6006.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6007 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6007, g_c)
                 else
                   (let uu____6010 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6010, g_c)))
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
                   let uu____6021 =
                     let uu____6022 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6022
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6021
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6025 =
                   let uu____6030 =
                     let uu____6031 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6031
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6030  in
                 match uu____6025 with
                 | (bind_c,g_bind) ->
                     let uu____6040 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6041 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6040, uu____6041))
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
            fun uu____6077  ->
              match uu____6077 with
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
                    let uu____6089 =
                      ((let uu____6093 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6093) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6089
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6111 =
        let uu____6112 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6112  in
      FStar_Syntax_Syntax.fvar uu____6111 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6182  ->
                 match uu____6182 with
                 | (uu____6196,eff_label,uu____6198,uu____6199) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6212 =
          let uu____6220 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6258  ->
                    match uu____6258 with
                    | (uu____6273,uu____6274,flags,uu____6276) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6293  ->
                                match uu___5_6293 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6296 -> false))))
             in
          if uu____6220
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6212 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6333 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6335 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6335
              then
                let uu____6342 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____6342, FStar_TypeChecker_Env.trivial_guard)
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6381 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6381 with
                   | (if_then_else1,uu____6391,uu____6392) ->
                       let uu____6393 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6394 =
                         let uu____6399 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6400 =
                           let uu____6401 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____6410 =
                             let uu____6421 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____6430 =
                               let uu____6441 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____6450 =
                                 let uu____6461 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____6461]  in
                               uu____6441 :: uu____6450  in
                             uu____6421 :: uu____6430  in
                           uu____6401 :: uu____6410  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6399 uu____6400
                          in
                       uu____6394 FStar_Pervasives_Native.None uu____6393
                    in
                 let default_case =
                   let post_k =
                     let uu____6514 =
                       let uu____6523 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6523]  in
                     let uu____6542 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6514 uu____6542  in
                   let kwp =
                     let uu____6548 =
                       let uu____6557 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6557]  in
                     let uu____6576 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6548 uu____6576  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6583 =
                       let uu____6584 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6584]  in
                     let uu____6603 =
                       let uu____6606 =
                         let uu____6613 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6613
                          in
                       let uu____6614 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6606 uu____6614  in
                     FStar_Syntax_Util.abs uu____6583 uu____6603
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
                   let uu____6638 =
                     should_not_inline_whole_match ||
                       (let uu____6641 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6641)
                      in
                   if uu____6638 then cthen true else cthen false  in
                 let uu____6648 =
                   FStar_List.fold_right
                     (fun uu____6694  ->
                        fun uu____6695  ->
                          match (uu____6694, uu____6695) with
                          | ((g,eff_label,uu____6737,cthen),(celse,g_comp))
                              ->
                              let uu____6771 =
                                let uu____6776 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____6776
                                 in
                              (match uu____6771 with
                               | (cthen1,gthen) ->
                                   let uu____6783 =
                                     lift_and_destruct env cthen1 celse  in
                                   (match uu____6783 with
                                    | ((md,uu____6813,uu____6814),(uu____6815,uu____6816,wp_then),
                                       (uu____6818,uu____6819,wp_else)) ->
                                        let uu____6839 =
                                          let uu____6840 =
                                            ifthenelse md res_t g wp_then
                                              wp_else
                                             in
                                          mk_comp md u_res_t res_t uu____6840
                                            []
                                           in
                                        let uu____6841 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_comp gthen
                                           in
                                        (uu____6839, uu____6841)))) lcases
                     (default_case, FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____6648 with
                 | (comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____6866::[] -> (comp, g_comp)
                      | uu____6909 ->
                          let comp1 =
                            FStar_TypeChecker_Env.comp_to_comp_typ env comp
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              comp1.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____6928 = destruct_comp comp1  in
                          (match uu____6928 with
                           | (uu____6939,uu____6940,wp) ->
                               let uu____6942 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   md.FStar_Syntax_Syntax.match_wps
                                  in
                               (match uu____6942 with
                                | (uu____6953,ite_wp,uu____6955) ->
                                    let wp1 =
                                      let uu____6959 =
                                        let uu____6964 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u_res_t] env md ite_wp
                                           in
                                        let uu____6965 =
                                          let uu____6966 =
                                            FStar_Syntax_Syntax.as_arg res_t
                                             in
                                          let uu____6975 =
                                            let uu____6986 =
                                              FStar_Syntax_Syntax.as_arg wp
                                               in
                                            [uu____6986]  in
                                          uu____6966 :: uu____6975  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____6964 uu____6965
                                         in
                                      uu____6959 FStar_Pervasives_Native.None
                                        wp.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____7019 =
                                      mk_comp md u_res_t res_t wp1
                                        bind_cases_flags
                                       in
                                    (uu____7019, g_comp)))))
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
          let uu____7053 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7053 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____7069 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____7075 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____7069 uu____7075
              else
                (let uu____7084 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____7090 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____7084 uu____7090)
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
          let uu____7115 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____7115
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____7118 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____7118
        then u_res
        else
          (let is_total =
             let uu____7125 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____7125
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____7136 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____7136 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7139 =
                    let uu____7145 =
                      let uu____7147 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____7147
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____7145)
                     in
                  FStar_Errors.raise_error uu____7139
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
      let uu____7171 = destruct_comp ct  in
      match uu____7171 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7190 = FStar_TypeChecker_Env.get_range env  in
            let uu____7191 =
              let uu____7196 =
                let uu____7197 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7197
                 in
              let uu____7200 =
                let uu____7201 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7210 =
                  let uu____7221 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7221]  in
                uu____7201 :: uu____7210  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7196 uu____7200  in
            uu____7191 FStar_Pervasives_Native.None uu____7190  in
          let uu____7254 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7254)
  
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
               let uu____7295 =
                 let uu____7296 = FStar_Syntax_Subst.compress t2  in
                 uu____7296.FStar_Syntax_Syntax.n  in
               match uu____7295 with
               | FStar_Syntax_Syntax.Tm_type uu____7300 -> true
               | uu____7302 -> false  in
             let uu____7304 =
               let uu____7305 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____7305.FStar_Syntax_Syntax.n  in
             match uu____7304 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7313 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7323 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7323
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7326 =
                     let uu____7327 =
                       let uu____7328 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7328
                        in
                     (FStar_Pervasives_Native.None, uu____7327)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7326
                    in
                 let e1 =
                   let uu____7334 =
                     let uu____7339 =
                       let uu____7340 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7340]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7339  in
                   uu____7334 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7365 -> (e, lc))
  
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
          (let uu____7400 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7400
           then
             let uu____7403 = FStar_Syntax_Print.term_to_string e  in
             let uu____7405 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____7407 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7403 uu____7405 uu____7407
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7417 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____7417 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7442 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7468 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____7468, false)
             else
               (let uu____7478 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____7478, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7491) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____7503 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____7503
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___940_7519 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___940_7519.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___940_7519.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___940_7519.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____7526 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____7526 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____7542 =
                      let uu____7543 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____7543 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____7563 =
                            let uu____7565 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____7565 = FStar_Syntax_Util.Equal  in
                          if uu____7563
                          then
                            ((let uu____7572 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7572
                              then
                                let uu____7576 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____7578 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____7576 uu____7578
                              else ());
                             (let uu____7583 = set_result_typ1 c  in
                              (uu____7583, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____7590 ->
                                   true
                               | uu____7598 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____7607 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____7607
                                  in
                               let lc1 =
                                 let uu____7609 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____7610 =
                                   let uu____7611 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____7611)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____7609 uu____7610
                                  in
                               ((let uu____7615 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7615
                                 then
                                   let uu____7619 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____7621 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____7623 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____7625 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____7619 uu____7621 uu____7623
                                     uu____7625
                                 else ());
                                (let uu____7630 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____7630 with
                                 | (c1,g_lc) ->
                                     let uu____7641 = set_result_typ1 c1  in
                                     let uu____7642 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____7641, uu____7642)))
                             else
                               ((let uu____7646 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7646
                                 then
                                   let uu____7650 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____7652 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____7650 uu____7652
                                 else ());
                                (let uu____7657 = set_result_typ1 c  in
                                 (uu____7657, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___977_7661 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___977_7661.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___977_7661.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___977_7661.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____7671 =
                      let uu____7672 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____7672
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____7682 =
                           let uu____7683 = FStar_Syntax_Subst.compress f1
                              in
                           uu____7683.FStar_Syntax_Syntax.n  in
                         match uu____7682 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____7690,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____7692;
                                           FStar_Syntax_Syntax.vars =
                                             uu____7693;_},uu____7694)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___993_7720 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___993_7720.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___993_7720.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___993_7720.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____7721 ->
                             let uu____7722 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____7722 with
                              | (c,g_c) ->
                                  ((let uu____7734 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7734
                                    then
                                      let uu____7738 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____7740 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____7742 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____7744 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____7738 uu____7740 uu____7742
                                        uu____7744
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
                                        let uu____7757 =
                                          let uu____7762 =
                                            let uu____7763 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____7763]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____7762
                                           in
                                        uu____7757
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____7790 =
                                      let uu____7795 =
                                        FStar_All.pipe_left
                                          (fun _7816  ->
                                             FStar_Pervasives_Native.Some
                                               _7816)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____7817 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____7818 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____7819 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____7795
                                        uu____7817 e uu____7818 uu____7819
                                       in
                                    match uu____7790 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1011_7827 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1011_7827.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1011_7827.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____7829 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____7829
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____7832 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____7832 with
                                         | (c2,g_lc) ->
                                             ((let uu____7844 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____7844
                                               then
                                                 let uu____7848 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____7848
                                               else ());
                                              (let uu____7853 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____7853))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_7862  ->
                              match uu___6_7862 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____7865 -> []))
                       in
                    let lc1 =
                      let uu____7867 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____7867 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1027_7869 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1027_7869.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1027_7869.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1027_7869.FStar_TypeChecker_Common.implicits)
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
        let uu____7905 =
          let uu____7908 =
            let uu____7913 =
              let uu____7914 =
                let uu____7923 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7923  in
              [uu____7914]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7913  in
          uu____7908 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7905  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____7946 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7946
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7965 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7981 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7998 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7998
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____8014)::(ens,uu____8016)::uu____8017 ->
                    let uu____8060 =
                      let uu____8063 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____8063  in
                    let uu____8064 =
                      let uu____8065 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____8065  in
                    (uu____8060, uu____8064)
                | uu____8068 ->
                    let uu____8079 =
                      let uu____8085 =
                        let uu____8087 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8087
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8085)
                       in
                    FStar_Errors.raise_error uu____8079
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8107)::uu____8108 ->
                    let uu____8135 =
                      let uu____8140 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8140
                       in
                    (match uu____8135 with
                     | (us_r,uu____8172) ->
                         let uu____8173 =
                           let uu____8178 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8178
                            in
                         (match uu____8173 with
                          | (us_e,uu____8210) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8213 =
                                  let uu____8214 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8214
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8213
                                  us_r
                                 in
                              let as_ens =
                                let uu____8216 =
                                  let uu____8217 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8217
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8216
                                  us_e
                                 in
                              let req =
                                let uu____8221 =
                                  let uu____8226 =
                                    let uu____8227 =
                                      let uu____8238 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8238]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8227
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8226
                                   in
                                uu____8221 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8278 =
                                  let uu____8283 =
                                    let uu____8284 =
                                      let uu____8295 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8295]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8284
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8283
                                   in
                                uu____8278 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8332 =
                                let uu____8335 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8335  in
                              let uu____8336 =
                                let uu____8337 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8337  in
                              (uu____8332, uu____8336)))
                | uu____8340 -> failwith "Impossible"))
  
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
      (let uu____8374 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8374
       then
         let uu____8379 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8381 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8379 uu____8381
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
        (let uu____8435 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8435
         then
           let uu____8440 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8442 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8440
             uu____8442
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8453 =
      let uu____8455 =
        let uu____8456 = FStar_Syntax_Subst.compress t  in
        uu____8456.FStar_Syntax_Syntax.n  in
      match uu____8455 with
      | FStar_Syntax_Syntax.Tm_app uu____8460 -> false
      | uu____8478 -> true  in
    if uu____8453
    then t
    else
      (let uu____8483 = FStar_Syntax_Util.head_and_args t  in
       match uu____8483 with
       | (head1,args) ->
           let uu____8526 =
             let uu____8528 =
               let uu____8529 = FStar_Syntax_Subst.compress head1  in
               uu____8529.FStar_Syntax_Syntax.n  in
             match uu____8528 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8534 -> false  in
           if uu____8526
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8566 ->
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
          ((let uu____8613 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____8613
            then
              let uu____8616 = FStar_Syntax_Print.term_to_string e  in
              let uu____8618 = FStar_Syntax_Print.term_to_string t  in
              let uu____8620 =
                let uu____8622 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____8622
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____8616 uu____8618 uu____8620
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____8635 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____8635 with
              | (formals,uu____8651) ->
                  let n_implicits =
                    let uu____8673 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____8751  ->
                              match uu____8751 with
                              | (uu____8759,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____8766 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____8766 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____8673 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____8891 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____8891 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____8905 =
                      let uu____8911 =
                        let uu____8913 = FStar_Util.string_of_int n_expected
                           in
                        let uu____8915 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____8917 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____8913 uu____8915 uu____8917
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____8911)
                       in
                    let uu____8921 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____8905 uu____8921
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_8939 =
              match uu___7_8939 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____8982 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____8982 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _9113,uu____9100) when
                           _9113 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____9146,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____9148))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9182 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9182 with
                            | (v1,uu____9223,g) ->
                                ((let uu____9238 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9238
                                  then
                                    let uu____9241 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9241
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9251 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9251 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9344 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9344))))
                       | (uu____9371,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9408 =
                             let uu____9421 =
                               let uu____9428 =
                                 let uu____9433 = FStar_Dyn.mkdyn env  in
                                 (uu____9433, tau)  in
                               FStar_Pervasives_Native.Some uu____9428  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9421
                              in
                           (match uu____9408 with
                            | (v1,uu____9466,g) ->
                                ((let uu____9481 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9481
                                  then
                                    let uu____9484 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9484
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9494 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9494 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9587 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9587))))
                       | (uu____9614,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____9662 =
                       let uu____9689 = inst_n_binders t1  in
                       aux [] uu____9689 bs1  in
                     (match uu____9662 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____9761) -> (e, torig, guard)
                           | (uu____9792,[]) when
                               let uu____9823 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____9823 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____9825 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____9853 ->
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
            | uu____9866 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9878 =
      let uu____9882 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9882
        (FStar_List.map
           (fun u  ->
              let uu____9894 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9894 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9878 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9922 = FStar_Util.set_is_empty x  in
      if uu____9922
      then []
      else
        (let s =
           let uu____9940 =
             let uu____9943 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9943  in
           FStar_All.pipe_right uu____9940 FStar_Util.set_elements  in
         (let uu____9959 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9959
          then
            let uu____9964 =
              let uu____9966 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9966  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9964
          else ());
         (let r =
            let uu____9975 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9975  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____10014 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____10014
                     then
                       let uu____10019 =
                         let uu____10021 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____10021
                          in
                       let uu____10025 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____10027 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____10019 uu____10025 uu____10027
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
        let uu____10057 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____10057 FStar_Util.set_elements  in
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
        | ([],uu____10096) -> generalized_univ_names
        | (uu____10103,[]) -> explicit_univ_names
        | uu____10110 ->
            let uu____10119 =
              let uu____10125 =
                let uu____10127 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____10127
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____10125)
               in
            FStar_Errors.raise_error uu____10119 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10149 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10149
       then
         let uu____10154 = FStar_Syntax_Print.term_to_string t  in
         let uu____10156 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10154 uu____10156
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10165 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10165
        then
          let uu____10170 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10170
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10179 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10179
         then
           let uu____10184 = FStar_Syntax_Print.term_to_string t  in
           let uu____10186 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10184 uu____10186
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
        let uu____10270 =
          let uu____10272 =
            FStar_Util.for_all
              (fun uu____10286  ->
                 match uu____10286 with
                 | (uu____10296,uu____10297,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10272  in
        if uu____10270
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10349 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10349
              then
                let uu____10352 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10352
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10359 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10359
               then
                 let uu____10362 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10362
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10380 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10380 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10414 =
             match uu____10414 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10451 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10451
                   then
                     let uu____10456 =
                       let uu____10458 =
                         let uu____10462 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10462
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10458
                         (FStar_String.concat ", ")
                        in
                     let uu____10510 =
                       let uu____10512 =
                         let uu____10516 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10516
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10529 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10531 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10529
                                   uu____10531))
                          in
                       FStar_All.pipe_right uu____10512
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10456
                       uu____10510
                   else ());
                  (let univs2 =
                     let uu____10545 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10557 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10557) univs1
                       uu____10545
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10564 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10564
                    then
                      let uu____10569 =
                        let uu____10571 =
                          let uu____10575 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10575
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10571
                          (FStar_String.concat ", ")
                         in
                      let uu____10623 =
                        let uu____10625 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10639 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10641 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10639
                                    uu____10641))
                           in
                        FStar_All.pipe_right uu____10625
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10569 uu____10623
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10662 =
             let uu____10679 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10679  in
           match uu____10662 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10769 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10769
                 then ()
                 else
                   (let uu____10774 = lec_hd  in
                    match uu____10774 with
                    | (lb1,uu____10782,uu____10783) ->
                        let uu____10784 = lec2  in
                        (match uu____10784 with
                         | (lb2,uu____10792,uu____10793) ->
                             let msg =
                               let uu____10796 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10798 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10796 uu____10798
                                in
                             let uu____10801 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10801))
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
                 let uu____10869 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10869
                 then ()
                 else
                   (let uu____10874 = lec_hd  in
                    match uu____10874 with
                    | (lb1,uu____10882,uu____10883) ->
                        let uu____10884 = lec2  in
                        (match uu____10884 with
                         | (lb2,uu____10892,uu____10893) ->
                             let msg =
                               let uu____10896 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10898 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10896 uu____10898
                                in
                             let uu____10901 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10901))
                  in
               let lecs1 =
                 let uu____10912 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10965 = univs_and_uvars_of_lec this_lec  in
                        match uu____10965 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10912 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____11070 = lec_hd  in
                   match uu____11070 with
                   | (lbname,e,c) ->
                       let uu____11080 =
                         let uu____11086 =
                           let uu____11088 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____11090 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____11092 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____11088 uu____11090 uu____11092
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____11086)
                          in
                       let uu____11096 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____11080 uu____11096
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____11115 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____11115 with
                         | FStar_Pervasives_Native.Some uu____11124 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____11132 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____11136 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____11136 with
                              | (bs,kres) ->
                                  ((let uu____11180 =
                                      let uu____11181 =
                                        let uu____11184 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11184
                                         in
                                      uu____11181.FStar_Syntax_Syntax.n  in
                                    match uu____11180 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11185
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11189 =
                                          let uu____11191 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11191  in
                                        if uu____11189
                                        then fail1 kres
                                        else ()
                                    | uu____11196 -> fail1 kres);
                                   (let a =
                                      let uu____11198 =
                                        let uu____11201 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11204  ->
                                             FStar_Pervasives_Native.Some
                                               _11204) uu____11201
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11198
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11212 ->
                                          let uu____11221 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11221
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
                      (fun uu____11324  ->
                         match uu____11324 with
                         | (lbname,e,c) ->
                             let uu____11370 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11431 ->
                                   let uu____11444 = (e, c)  in
                                   (match uu____11444 with
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
                                                (fun uu____11484  ->
                                                   match uu____11484 with
                                                   | (x,uu____11490) ->
                                                       let uu____11491 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11491)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11509 =
                                                let uu____11511 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11511
                                                 in
                                              if uu____11509
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
                                          let uu____11520 =
                                            let uu____11521 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11521.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11520 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11546 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11546 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11557 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11561 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11561, gen_tvars))
                                in
                             (match uu____11370 with
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
        (let uu____11708 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11708
         then
           let uu____11711 =
             let uu____11713 =
               FStar_List.map
                 (fun uu____11728  ->
                    match uu____11728 with
                    | (lb,uu____11737,uu____11738) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11713 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11711
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11764  ->
                match uu____11764 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11793 = gen env is_rec lecs  in
           match uu____11793 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11892  ->
                       match uu____11892 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11954 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11954
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____12002  ->
                           match uu____12002 with
                           | (l,us,e,c,gvs) ->
                               let uu____12036 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____12038 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____12040 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____12042 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____12044 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____12036 uu____12038 uu____12040
                                 uu____12042 uu____12044))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____12089  ->
                match uu____12089 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____12133 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____12133, t, c, gvs)) univnames_lecs
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
              (let uu____12194 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12194 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12200 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12203  -> FStar_Pervasives_Native.Some _12203)
                     uu____12200)
             in
          let is_var e1 =
            let uu____12211 =
              let uu____12212 = FStar_Syntax_Subst.compress e1  in
              uu____12212.FStar_Syntax_Syntax.n  in
            match uu____12211 with
            | FStar_Syntax_Syntax.Tm_name uu____12216 -> true
            | uu____12218 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1483_12239 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1483_12239.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1483_12239.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12240 -> e2  in
          let env2 =
            let uu___1486_12242 = env1  in
            let uu____12243 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1486_12242.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1486_12242.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1486_12242.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1486_12242.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1486_12242.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1486_12242.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1486_12242.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1486_12242.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1486_12242.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1486_12242.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1486_12242.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1486_12242.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1486_12242.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1486_12242.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1486_12242.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1486_12242.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1486_12242.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12243;
              FStar_TypeChecker_Env.is_iface =
                (uu___1486_12242.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1486_12242.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1486_12242.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1486_12242.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1486_12242.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1486_12242.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1486_12242.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1486_12242.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1486_12242.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1486_12242.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1486_12242.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1486_12242.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1486_12242.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1486_12242.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1486_12242.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1486_12242.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1486_12242.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
                (uu___1493_12204.FStar_TypeChecker_Env.synth_hook);
=======
                (uu___1486_12242.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1486_12242.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
              FStar_TypeChecker_Env.splice =
                (uu___1486_12242.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1486_12242.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1486_12242.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1486_12242.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1486_12242.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1486_12242.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1486_12242.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1486_12242.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12245 = check1 env2 t1 t2  in
          match uu____12245 with
          | FStar_Pervasives_Native.None  ->
              let uu____12252 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12258 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12252 uu____12258
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12265 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12265
                then
                  let uu____12270 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12270
                else ());
               (let uu____12276 = decorate e t2  in (uu____12276, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12304 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12304
         then
           let uu____12307 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12307
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12321 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____12321 with
         | (c,g_c) ->
             let uu____12333 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____12333
             then
               let uu____12341 =
                 let uu____12343 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____12343  in
               (uu____12341, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____12351 =
                    let uu____12352 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____12352
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____12351
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____12353 = check_trivial_precondition env c1  in
                match uu____12353 with
                | (ct,vc,g_pre) ->
                    ((let uu____12369 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____12369
                      then
                        let uu____12374 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____12374
                      else ());
                     (let uu____12379 =
                        let uu____12381 =
                          let uu____12382 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____12382  in
                        discharge uu____12381  in
                      let uu____12383 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____12379, uu____12383)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12417 =
        match uu___8_12417 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12427)::[] -> f fst1
        | uu____12452 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12464 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12464
          (fun _12465  -> FStar_TypeChecker_Common.NonTrivial _12465)
         in
      let op_or_e e =
        let uu____12476 =
          let uu____12477 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12477  in
        FStar_All.pipe_right uu____12476
          (fun _12480  -> FStar_TypeChecker_Common.NonTrivial _12480)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12487  -> FStar_TypeChecker_Common.NonTrivial _12487)
         in
      let op_or_t t =
        let uu____12498 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12498
          (fun _12501  -> FStar_TypeChecker_Common.NonTrivial _12501)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12508  -> FStar_TypeChecker_Common.NonTrivial _12508)
         in
      let short_op_ite uu___9_12514 =
        match uu___9_12514 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12524)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12551)::[] ->
            let uu____12592 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12592
              (fun _12593  -> FStar_TypeChecker_Common.NonTrivial _12593)
        | uu____12594 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12606 =
          let uu____12614 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12614)  in
        let uu____12622 =
          let uu____12632 =
            let uu____12640 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12640)  in
          let uu____12648 =
            let uu____12658 =
              let uu____12666 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12666)  in
            let uu____12674 =
              let uu____12684 =
                let uu____12692 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12692)  in
              let uu____12700 =
                let uu____12710 =
                  let uu____12718 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12718)  in
                [uu____12710; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12684 :: uu____12700  in
            uu____12658 :: uu____12674  in
          uu____12632 :: uu____12648  in
        uu____12606 :: uu____12622  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12780 =
            FStar_Util.find_map table
              (fun uu____12795  ->
                 match uu____12795 with
                 | (x,mk1) ->
                     let uu____12812 = FStar_Ident.lid_equals x lid  in
                     if uu____12812
                     then
                       let uu____12817 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12817
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12780 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12821 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12829 =
      let uu____12830 = FStar_Syntax_Util.un_uinst l  in
      uu____12830.FStar_Syntax_Syntax.n  in
    match uu____12829 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12835 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12871)::uu____12872 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12891 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12900,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12901))::uu____12902 -> bs
      | uu____12920 ->
          let uu____12921 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12921 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12925 =
                 let uu____12926 = FStar_Syntax_Subst.compress t  in
                 uu____12926.FStar_Syntax_Syntax.n  in
               (match uu____12925 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12930) ->
                    let uu____12951 =
                      FStar_Util.prefix_until
                        (fun uu___10_12991  ->
                           match uu___10_12991 with
                           | (uu____12999,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____13000)) ->
                               false
                           | uu____13005 -> true) bs'
                       in
                    (match uu____12951 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____13041,uu____13042) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____13114,uu____13115) ->
                         let uu____13188 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13208  ->
                                   match uu____13208 with
                                   | (x,uu____13217) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13188
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13266  ->
                                     match uu____13266 with
                                     | (x,i) ->
                                         let uu____13285 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13285, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13296 -> bs))
  
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
            let uu____13325 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13325
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
          let uu____13356 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13356
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
        (let uu____13399 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13399
         then
           ((let uu____13404 = FStar_Ident.text_of_lid lident  in
             d uu____13404);
            (let uu____13406 = FStar_Ident.text_of_lid lident  in
             let uu____13408 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13406 uu____13408))
         else ());
        (let fv =
           let uu____13414 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13414
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
         let uu____13426 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1643_13428 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1643_13428.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1643_13428.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1643_13428.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1643_13428.FStar_Syntax_Syntax.sigattrs)
           }), uu____13426))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13446 =
        match uu___11_13446 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13449 -> false  in
      let reducibility uu___12_13457 =
        match uu___12_13457 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13464 -> false  in
      let assumption uu___13_13472 =
        match uu___13_13472 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13476 -> false  in
      let reification uu___14_13484 =
        match uu___14_13484 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13487 -> true
        | uu____13489 -> false  in
      let inferred uu___15_13497 =
        match uu___15_13497 with
        | FStar_Syntax_Syntax.Discriminator uu____13499 -> true
        | FStar_Syntax_Syntax.Projector uu____13501 -> true
        | FStar_Syntax_Syntax.RecordType uu____13507 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13517 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13530 -> false  in
      let has_eq uu___16_13538 =
        match uu___16_13538 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13542 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____13621 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13628 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____13639 =
        let uu____13641 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_13647  ->
                  match uu___17_13647 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____13650 -> false))
           in
        FStar_All.pipe_right uu____13641 Prims.op_Negation  in
      if uu____13639
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____13671 =
            let uu____13677 =
              let uu____13679 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____13679 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____13677)  in
          FStar_Errors.raise_error uu____13671 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____13697 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____13705 =
            let uu____13707 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____13707  in
          if uu____13705 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____13717),uu____13718) ->
              ((let uu____13730 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____13730
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____13739 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____13739
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13750 ->
              let uu____13759 =
                let uu____13761 =
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
                Prims.op_Negation uu____13761  in
              if uu____13759 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13771 ->
              let uu____13778 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13778 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13786 ->
              let uu____13793 =
                let uu____13795 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13795  in
              if uu____13793 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13805 ->
              let uu____13806 =
                let uu____13808 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13808  in
              if uu____13806 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13818 ->
              let uu____13819 =
                let uu____13821 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13821  in
              if uu____13819 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13831 ->
              let uu____13844 =
                let uu____13846 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13846  in
              if uu____13844 then err'1 () else ()
          | uu____13856 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____13879 =
          let uu____13884 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____13884
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____13879
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____13903 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____13903
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____13921 =
                          let uu____13922 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13922.FStar_Syntax_Syntax.n  in
                        match uu____13921 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____13928 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____13954 =
          let uu____13955 = FStar_Syntax_Subst.compress t1  in
          uu____13955.FStar_Syntax_Syntax.n  in
        match uu____13954 with
        | FStar_Syntax_Syntax.Tm_type uu____13959 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____13962 ->
            let uu____13977 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13977 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____14010 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____14010
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____14016;
               FStar_Syntax_Syntax.index = uu____14017;
               FStar_Syntax_Syntax.sort = t2;_},uu____14019)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____14028,uu____14029) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____14071::[]) ->
            let uu____14110 =
              let uu____14111 = FStar_Syntax_Util.un_uinst head1  in
              uu____14111.FStar_Syntax_Syntax.n  in
            (match uu____14110 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____14116 -> false)
        | uu____14118 -> false
      
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
        (let uu____14128 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____14128
         then
           let uu____14133 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____14133
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
                  let uu____14194 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14194 r  in
                let uu____14204 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14204 with
                | (uu____14213,signature) ->
                    let uu____14215 =
                      let uu____14216 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14216.FStar_Syntax_Syntax.n  in
                    (match uu____14215 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14224) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14272 =
                                FStar_List.fold_left
                                  (fun uu____14312  ->
                                     fun uu____14313  ->
                                       match (uu____14312, uu____14313) with
                                       | ((is,g,substs),(b,_t)) ->
                                           let reason =
                                             let uu____14391 =
                                               FStar_Syntax_Print.binder_to_string
                                                 (b, _t)
                                                in
                                             let uu____14395 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "uvar for binder %s when creating a fresh repr for %s at %s"
                                               uu____14391
                                               eff_name.FStar_Ident.str
                                               uu____14395
                                              in
                                           let uu____14398 =
                                             let uu____14411 =
                                               FStar_Syntax_Subst.subst
                                                 substs
                                                 b.FStar_Syntax_Syntax.sort
                                                in
                                             new_implicit_var reason r env
                                               uu____14411
                                              in
                                           (match uu____14398 with
                                            | (t,uu____14423,g_t) ->
                                                let uu____14437 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g g_t
                                                   in
                                                ((FStar_List.append is [t]),
                                                  uu____14437,
                                                  (FStar_List.append substs
                                                     [FStar_Syntax_Syntax.NT
                                                        (b, t)]))))
                                  ([], FStar_TypeChecker_Env.trivial_guard,
                                    [FStar_Syntax_Syntax.NT
                                       ((FStar_Pervasives_Native.fst a),
                                         a_tm)]) bs2
                                 in
                              (match uu____14272 with
                               | (is,g,uu____14458) ->
                                   let repr =
                                     let uu____14468 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14468
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14477 =
                                     let uu____14478 =
                                       let uu____14483 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14483
                                        in
                                     uu____14478 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14477, g))
                          | uu____14492 -> fail1 signature)
                     | uu____14493 -> fail1 signature)
  
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
            let uu____14524 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____14524
              (fun ed  ->
                 fresh_layered_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature
                   ed.FStar_Syntax_Syntax.repr u a_tm)
  
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
              let uu____14562 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____14562 with
              | (uu____14567,sig_tm) ->
                  let fail1 t =
                    let uu____14575 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____14575 r  in
                  let uu____14581 =
                    let uu____14582 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____14582.FStar_Syntax_Syntax.n  in
                  (match uu____14581 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14586) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____14609)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____14631 -> fail1 sig_tm)
                   | uu____14632 -> fail1 sig_tm)
  