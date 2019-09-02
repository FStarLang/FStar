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
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let c1 =
          let uu____1068 =
            let uu____1073 =
              FStar_All.pipe_right c FStar_Syntax_Syntax.mk_Comp  in
            FStar_All.pipe_right uu____1073
              (lift.FStar_TypeChecker_Env.mlift_wp env)
             in
          FStar_All.pipe_right uu____1068
            (fun uu____1085  ->
               match uu____1085 with
               | (c1,g) -> FStar_Syntax_Util.comp_to_comp_typ c1)
           in
        let uu___170_1092 = c1  in
        {
          FStar_Syntax_Syntax.comp_univs =
            (uu___170_1092.FStar_Syntax_Syntax.comp_univs);
          FStar_Syntax_Syntax.effect_name =
            (uu___170_1092.FStar_Syntax_Syntax.effect_name);
          FStar_Syntax_Syntax.result_typ =
            (uu___170_1092.FStar_Syntax_Syntax.result_typ);
          FStar_Syntax_Syntax.effect_args =
            (uu___170_1092.FStar_Syntax_Syntax.effect_args);
          FStar_Syntax_Syntax.flags = []
        }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1109 =
          let uu____1116 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1117 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1116 uu____1117  in
        match uu____1109 with | (m,uu____1119,uu____1120) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1137 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1137
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
        let uu____1184 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1184 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp env c11 lift1  in
            let m2 = lift_comp env c21 lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____1221 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____1221 with
             | (a,kwp) ->
                 let uu____1252 = destruct_comp m1  in
                 let uu____1259 = destruct_comp m2  in
                 ((md, a, kwp), uu____1252, uu____1259))
  
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
            let uu____1344 =
              let uu____1345 =
                let uu____1356 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1356]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1345;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1344
  
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
          let uu____1440 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1440
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1452 =
      let uu____1453 = FStar_Syntax_Subst.compress t  in
      uu____1453.FStar_Syntax_Syntax.n  in
    match uu____1452 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1457 -> true
    | uu____1473 -> false
  
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
              let uu____1543 =
                let uu____1545 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1545  in
              if uu____1543
              then f
              else (let uu____1552 = reason1 ()  in label uu____1552 r f)
  
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
            let uu___236_1573 = g  in
            let uu____1574 =
              let uu____1575 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1575  in
            {
              FStar_TypeChecker_Common.guard_f = uu____1574;
              FStar_TypeChecker_Common.deferred =
                (uu___236_1573.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___236_1573.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___236_1573.FStar_TypeChecker_Common.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1596 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1596
        then c
        else
          (let uu____1601 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1601
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let uu____1642 =
                  FStar_Syntax_Util.get_match_with_close_wps
                    md.FStar_Syntax_Syntax.match_wps
                   in
                match uu____1642 with
                | (uu____1651,uu____1652,close1) ->
                    FStar_List.fold_right
                      (fun x  ->
                         fun wp  ->
                           let bs =
                             let uu____1675 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____1675]  in
                           let us =
                             let uu____1697 =
                               let uu____1700 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               [uu____1700]  in
                             u_res :: uu____1697  in
                           let wp1 =
                             FStar_Syntax_Util.abs bs wp
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None
                                     [FStar_Syntax_Syntax.TOTAL]))
                              in
                           let uu____1706 =
                             let uu____1711 =
                               FStar_TypeChecker_Env.inst_effect_fun_with us
                                 env md close1
                                in
                             let uu____1712 =
                               let uu____1713 =
                                 FStar_Syntax_Syntax.as_arg res_t  in
                               let uu____1722 =
                                 let uu____1733 =
                                   FStar_Syntax_Syntax.as_arg
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____1742 =
                                   let uu____1753 =
                                     FStar_Syntax_Syntax.as_arg wp1  in
                                   [uu____1753]  in
                                 uu____1733 :: uu____1742  in
                               uu____1713 :: uu____1722  in
                             FStar_Syntax_Syntax.mk_Tm_app uu____1711
                               uu____1712
                              in
                           uu____1706 FStar_Pervasives_Native.None
                             wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1795 = destruct_comp c1  in
              match uu____1795 with
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
                let uu____1835 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____1835
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
              ({ FStar_Syntax_Syntax.ppname = uu____1858;
                 FStar_Syntax_Syntax.index = uu____1859;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____1861;
                     FStar_Syntax_Syntax.vars = uu____1862;_};_},uu____1863)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____1871 -> c
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_1883  ->
            match uu___0_1883 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1886 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____1911 =
            let uu____1914 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____1914 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____1911
            (fun c  ->
               (let uu____1970 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____1970) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____1974 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____1974)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____1985 = FStar_Syntax_Util.head_and_args' e  in
                match uu____1985 with
                | (head1,uu____2002) ->
                    let uu____2023 =
                      let uu____2024 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2024.FStar_Syntax_Syntax.n  in
                    (match uu____2023 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2029 =
                           let uu____2031 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2031
                            in
                         Prims.op_Negation uu____2029
                     | uu____2032 -> true)))
              &&
              (let uu____2035 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2035)
  
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
            let uu____2063 =
              let uu____2065 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2065  in
            if uu____2063
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2072 = FStar_Syntax_Util.is_unit t  in
               if uu____2072
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
                    let uu____2081 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2081
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2086 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2086 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2096 =
                             let uu____2097 =
                               let uu____2102 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2103 =
                                 let uu____2104 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2113 =
                                   let uu____2124 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2124]  in
                                 uu____2104 :: uu____2113  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2102
                                 uu____2103
                                in
                             uu____2097 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2096)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2158 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2158
           then
             let uu____2163 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2165 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2167 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2163 uu____2165 uu____2167
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
                let uu____2205 =
                  FStar_TypeChecker_Env.monad_leq env
                    FStar_Parser_Const.effect_PURE_lid
                    md.FStar_Syntax_Syntax.mname
                   in
                match uu____2205 with
                | FStar_Pervasives_Native.Some edge -> edge
                | FStar_Pervasives_Native.None  ->
                    failwith
                      (Prims.op_Hat
                         "Impossible! lift_wp_and_bind_with: did not find a lift from PURE to "
                         (md.FStar_Syntax_Syntax.mname).FStar_Ident.str)
                 in
              let wp11 =
                let c =
                  let uu____2214 =
                    let uu____2215 =
                      let uu____2226 =
                        FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg
                         in
                      [uu____2226]  in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        [FStar_Syntax_Syntax.U_zero];
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        FStar_Syntax_Syntax.t_unit;
                      FStar_Syntax_Syntax.effect_args = uu____2215;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____2214  in
                let uu____2259 =
                  FStar_All.pipe_right c
                    ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                       env)
                   in
                FStar_All.pipe_right uu____2259
                  (fun uu____2278  ->
                     match uu____2278 with
                     | (c1,g) ->
                         let uu____2287 =
                           FStar_All.pipe_right c1
                             FStar_Syntax_Util.comp_to_comp_typ
                            in
                         FStar_All.pipe_right uu____2287
                           (fun ct  ->
                              let uu____2293 =
                                FStar_All.pipe_right
                                  ct.FStar_Syntax_Syntax.effect_args
                                  FStar_List.hd
                                 in
                              FStar_All.pipe_right uu____2293
                                FStar_Pervasives_Native.fst))
                 in
              let uu____2342 =
                let uu____2347 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [FStar_Syntax_Syntax.U_zero; u_res_t] env md
                    md.FStar_Syntax_Syntax.bind_wp
                   in
                let uu____2348 =
                  let uu____2349 =
                    let uu____2358 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_range r))
                        FStar_Pervasives_Native.None r
                       in
                    FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2358
                     in
                  let uu____2367 =
                    let uu____2378 =
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2395 =
                      let uu____2406 = FStar_Syntax_Syntax.as_arg res_t  in
                      let uu____2415 =
                        let uu____2426 = FStar_Syntax_Syntax.as_arg wp11  in
                        let uu____2435 =
                          let uu____2446 =
                            let uu____2455 =
                              let uu____2456 =
                                let uu____2457 =
                                  FStar_Syntax_Syntax.null_binder
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                [uu____2457]  in
                              FStar_Syntax_Util.abs uu____2456 wp2
                                (FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Util.mk_residual_comp
                                      FStar_Parser_Const.effect_Tot_lid
                                      FStar_Pervasives_Native.None
                                      [FStar_Syntax_Syntax.TOTAL]))
                               in
                            FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                              uu____2455
                             in
                          [uu____2446]  in
                        uu____2426 :: uu____2435  in
                      uu____2406 :: uu____2415  in
                    uu____2378 :: uu____2395  in
                  uu____2349 :: uu____2367  in
                FStar_Syntax_Syntax.mk_Tm_app uu____2347 uu____2348  in
              uu____2342 FStar_Pervasives_Native.None
                wp2.FStar_Syntax_Syntax.pos
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____2546 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_2552  ->
              match uu___1_2552 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____2555 -> false))
       in
    if uu____2546
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_2567  ->
              match uu___2_2567 with
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
        let uu____2587 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2587
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____2593 = destruct_comp c1  in
           match uu____2593 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assume_wp =
                 let uu____2606 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assume_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____2606  in
               let pure_assume_wp1 =
                 let uu____2611 =
                   let uu____2616 =
                     let uu____2617 =
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula
                        in
                     [uu____2617]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____2616
                    in
                 uu____2611 FStar_Pervasives_Native.None r  in
               let w_wp =
                 lift_wp_and_bind_with env pure_assume_wp1 md u_res_t res_t
                   wp
                  in
               let uu____2651 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t w_wp uu____2651)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2679 =
          let uu____2680 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____2680 with
          | (c,g_c) ->
              let uu____2691 =
                let uu____2692 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____2692
                then c
                else
                  (match f with
                   | FStar_TypeChecker_Common.Trivial  -> c
                   | FStar_TypeChecker_Common.NonTrivial f1 ->
                       weaken_comp env c f1)
                 in
              (uu____2691, g_c)
           in
        let uu____2698 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____2698 weaken
  
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
               let uu____2747 = destruct_comp c1  in
               match uu____2747 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let pure_assert_wp =
                     let uu____2759 =
                       FStar_Syntax_Syntax.lid_as_fv
                         FStar_Parser_Const.pure_assert_wp_lid
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____2759  in
                   let pure_assert_wp1 =
                     let uu____2764 =
                       let uu____2769 =
                         let uu____2770 =
                           let uu____2779 = label_opt env reason r f  in
                           FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                             uu____2779
                            in
                         [uu____2770]  in
                       FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp
                         uu____2769
                        in
                     uu____2764 FStar_Pervasives_Native.None r  in
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
            let uu____2850 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____2850
            then (lc, g0)
            else
              (let flags =
                 let uu____2862 =
                   let uu____2870 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____2870
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____2862 with
                 | (maybe_trivial_post,flags) ->
                     let uu____2900 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_2908  ->
                               match uu___3_2908 with
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
                               | uu____2911 -> []))
                        in
                     FStar_List.append flags uu____2900
                  in
               let strengthen uu____2921 =
                 let uu____2922 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____2922 with
                 | (c,g_c) ->
                     let uu____2933 =
                       if env.FStar_TypeChecker_Env.lax
                       then c
                       else
                         (let g01 =
                            FStar_TypeChecker_Rel.simplify_guard env g0  in
                          let uu____2938 =
                            FStar_TypeChecker_Env.guard_form g01  in
                          match uu____2938 with
                          | FStar_TypeChecker_Common.Trivial  -> c
                          | FStar_TypeChecker_Common.NonTrivial f ->
                              ((let uu____2941 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    FStar_Options.Extreme
                                   in
                                if uu____2941
                                then
                                  let uu____2945 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env e_for_debugging_only
                                     in
                                  let uu____2947 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env f
                                     in
                                  FStar_Util.print2
                                    "-------------Strengthening pre-condition of term %s with guard %s\n"
                                    uu____2945 uu____2947
                                else ());
                               strengthen_comp env reason c f flags))
                        in
                     (uu____2933, g_c)
                  in
               let uu____2952 =
                 let uu____2953 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____2953
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____2952,
                 (let uu___423_2955 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___423_2955.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___423_2955.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___423_2955.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_2964  ->
            match uu___4_2964 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____2968 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____2997 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____2997
          then e
          else
            (let uu____3004 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____3007 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____3007)
                in
             if uu____3004
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
          fun uu____3060  ->
            match uu____3060 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____3080 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____3080 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____3093 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____3093
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____3103 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____3103
                       then
                         let uu____3108 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____3108
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____3115 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____3115
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____3124 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____3124
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____3131 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____3131
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____3147 =
                  let uu____3148 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3148
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____3156 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____3156, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____3159 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____3159 with
                     | (c1,g_c1) ->
                         let uu____3170 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____3170 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____3190  ->
                                    let uu____3191 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____3193 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____3198 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____3191 uu____3193 uu____3198);
                               (let aux uu____3216 =
                                  let uu____3217 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____3217
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____3248
                                        ->
                                        let uu____3249 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____3249
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____3281 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____3281
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____3326 =
                                  let uu____3327 =
                                    let uu____3329 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____3329  in
                                  if uu____3327
                                  then
                                    let uu____3343 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____3343
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____3366 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____3366))
                                  else
                                    (let uu____3381 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____3381
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___493_3423 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___493_3423.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___493_3423.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____3424 =
                                           let uu____3430 =
                                             close_comp_if_refinement_t env
                                               x1.FStar_Syntax_Syntax.sort x1
                                               c
                                              in
                                           (uu____3430, reason)  in
                                         FStar_Util.Inl uu____3424  in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____3466 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____3466
                                             (close1 x "c1 Tot")
                                       | (uu____3480,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____3503,uu____3504) -> aux ()
                                     else
                                       (let uu____3519 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____3519
                                        then
                                          let uu____3532 =
                                            let uu____3538 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____3538, "both GTot")  in
                                          FStar_Util.Inl uu____3532
                                        else aux ()))
                                   in
                                let uu____3549 = try_simplify ()  in
                                match uu____3549 with
                                | FStar_Util.Inl (c,reason) ->
                                    (debug1
                                       (fun uu____3579  ->
                                          let uu____3580 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____3580);
                                     (let uu____3583 =
                                        FStar_TypeChecker_Env.conj_guard g_c1
                                          g_c2
                                         in
                                      (c, uu____3583)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____3595  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_layered_bind c11 b1 c21 =
                                        (let uu____3622 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other
                                                "LayeredEffects")
                                            in
                                         if uu____3622
                                         then
                                           let uu____3627 =
                                             FStar_Syntax_Print.comp_to_string
                                               c11
                                              in
                                           let uu____3629 =
                                             FStar_Syntax_Print.comp_to_string
                                               c21
                                              in
                                           FStar_Util.print2
                                             "Binding c1:%s and c2:%s {\n"
                                             uu____3627 uu____3629
                                         else ());
                                        (let ct1 =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c11
                                            in
                                         let ct2 =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c21
                                            in
                                         let uu____3636 =
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
                                           let uu____3647 =
                                             FStar_TypeChecker_Env.monad_leq
                                               env
                                               c1_ed.FStar_Syntax_Syntax.mname
                                               c2_ed.FStar_Syntax_Syntax.mname
                                              in
                                           match uu____3647 with
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3658 =
                                                 FStar_TypeChecker_Env.monad_leq
                                                   env
                                                   c2_ed.FStar_Syntax_Syntax.mname
                                                   c1_ed.FStar_Syntax_Syntax.mname
                                                  in
                                               (match uu____3658 with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    let uu____3669 =
                                                      let uu____3675 =
                                                        FStar_Util.format2
                                                          "Effects %s and %s cannot be composed"
                                                          (c1_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                          (c2_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                         in
                                                      (FStar_Errors.Fatal_EffectsCannotBeComposed,
                                                        uu____3675)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3669 r1
                                                | FStar_Pervasives_Native.Some
                                                    edge ->
                                                    let uu____3688 =
                                                      let uu____3693 =
                                                        let uu____3698 =
                                                          FStar_All.pipe_right
                                                            ct2
                                                            FStar_Syntax_Syntax.mk_Comp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3698
                                                          ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                             env)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3693
                                                        (fun uu____3715  ->
                                                           match uu____3715
                                                           with
                                                           | (c,g) ->
                                                               let uu____3726
                                                                 =
                                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                                   c
                                                                  in
                                                               (uu____3726,
                                                                 g))
                                                       in
                                                    (match uu____3688 with
                                                     | (ct21,g_lift) ->
                                                         (ct1, ct21, c1_ed,
                                                           g_lift)))
                                           | FStar_Pervasives_Native.Some
                                               edge ->
                                               let uu____3738 =
                                                 let uu____3743 =
                                                   let uu____3748 =
                                                     FStar_All.pipe_right ct1
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3748
                                                     ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                        env)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3743
                                                   (fun uu____3765  ->
                                                      match uu____3765 with
                                                      | (c,g) ->
                                                          let uu____3776 =
                                                            FStar_Syntax_Util.comp_to_comp_typ
                                                              c
                                                             in
                                                          (uu____3776, g))
                                                  in
                                               (match uu____3738 with
                                                | (ct11,g_lift) ->
                                                    (ct11, ct2, c2_ed,
                                                      g_lift))
                                            in
                                         match uu____3636 with
                                         | (ct11,ct21,ed,g_lift) ->
                                             ((let uu____3796 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____3796
                                               then
                                                 let uu____3801 =
                                                   let uu____3803 =
                                                     FStar_All.pipe_right
                                                       ct11
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3803
                                                     FStar_Syntax_Print.comp_to_string
                                                    in
                                                 let uu____3805 =
                                                   let uu____3807 =
                                                     FStar_All.pipe_right
                                                       ct21
                                                       FStar_Syntax_Syntax.mk_Comp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3807
                                                     FStar_Syntax_Print.comp_to_string
                                                    in
                                                 FStar_Util.print2
                                                   "After lifting, ct1: %s and ct2: %s\n"
                                                   uu____3801 uu____3805
                                               else ());
                                              (let uu____3812 =
                                                 let uu____3823 =
                                                   FStar_List.hd
                                                     ct11.FStar_Syntax_Syntax.comp_univs
                                                    in
                                                 let uu____3824 =
                                                   FStar_List.map
                                                     FStar_Pervasives_Native.fst
                                                     ct11.FStar_Syntax_Syntax.effect_args
                                                    in
                                                 (uu____3823,
                                                   (ct11.FStar_Syntax_Syntax.result_typ),
                                                   uu____3824)
                                                  in
                                               match uu____3812 with
                                               | (u1,t1,is1) ->
                                                   let uu____3858 =
                                                     let uu____3869 =
                                                       FStar_List.hd
                                                         ct21.FStar_Syntax_Syntax.comp_univs
                                                        in
                                                     let uu____3870 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         ct21.FStar_Syntax_Syntax.effect_args
                                                        in
                                                     (uu____3869,
                                                       (ct21.FStar_Syntax_Syntax.result_typ),
                                                       uu____3870)
                                                      in
                                                   (match uu____3858 with
                                                    | (u2,t2,is2) ->
                                                        let uu____3904 =
                                                          FStar_TypeChecker_Env.inst_tscheme_with
                                                            ed.FStar_Syntax_Syntax.bind_wp
                                                            [u1; u2]
                                                           in
                                                        (match uu____3904
                                                         with
                                                         | (uu____3913,bind_t)
                                                             ->
                                                             let bind_t_shape_error
                                                               s =
                                                               let uu____3928
                                                                 =
                                                                 let uu____3930
                                                                   =
                                                                   FStar_Syntax_Print.term_to_string
                                                                    bind_t
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind %s does not have proper shape (reason:%s)"
                                                                   uu____3930
                                                                   s
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____3928)
                                                                in
                                                             let uu____3934 =
                                                               let uu____3979
                                                                 =
                                                                 let uu____3980
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    bind_t
                                                                    in
                                                                 uu____3980.FStar_Syntax_Syntax.n
                                                                  in
                                                               match uu____3979
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c)
                                                                   when
                                                                   (FStar_List.length
                                                                    bs) >=
                                                                    (Prims.of_int (4))
                                                                   ->
                                                                   let uu____4056
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____4056
                                                                    with
                                                                    | 
                                                                    (a_b::b_b::bs1,c3)
                                                                    ->
                                                                    let uu____4141
                                                                    =
                                                                    let uu____4168
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs1) -
                                                                    (Prims.of_int (2)))
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4168
                                                                    (fun
                                                                    uu____4253
                                                                     ->
                                                                    match uu____4253
                                                                    with
                                                                    | 
                                                                    (l1,l2)
                                                                    ->
                                                                    let uu____4334
                                                                    =
                                                                    FStar_List.hd
                                                                    l2  in
                                                                    let uu____4347
                                                                    =
                                                                    let uu____4354
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                    FStar_List.hd
                                                                    uu____4354
                                                                     in
                                                                    (l1,
                                                                    uu____4334,
                                                                    uu____4347))
                                                                     in
                                                                    (match uu____4141
                                                                    with
                                                                    | 
                                                                    (rest_bs,f_b,g_b)
                                                                    ->
                                                                    let uu____4482
                                                                    =
                                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                                    c3  in
                                                                    (a_b,
                                                                    b_b,
                                                                    rest_bs,
                                                                    f_b, g_b,
                                                                    uu____4482)))
                                                               | uu____4515
                                                                   ->
                                                                   let uu____4516
                                                                    =
                                                                    bind_t_shape_error
                                                                    "Either not an arrow or not enough binders"
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____4516
                                                                    r1
                                                                in
                                                             (match uu____3934
                                                              with
                                                              | (a_b,b_b,rest_bs,f_b,g_b,bind_ct)
                                                                  ->
                                                                  let uu____4641
                                                                    =
                                                                    let uu____4648
                                                                    =
                                                                    let uu____4649
                                                                    =
                                                                    let uu____4650
                                                                    =
                                                                    let uu____4657
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    a_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4657,
                                                                    t1)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4650
                                                                     in
                                                                    let uu____4668
                                                                    =
                                                                    let uu____4671
                                                                    =
                                                                    let uu____4672
                                                                    =
                                                                    let uu____4679
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4679,
                                                                    t2)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4672
                                                                     in
                                                                    [uu____4671]
                                                                     in
                                                                    uu____4649
                                                                    ::
                                                                    uu____4668
                                                                     in
                                                                    FStar_TypeChecker_Env.uvars_for_binders
                                                                    env
                                                                    rest_bs
                                                                    uu____4648
                                                                    (fun b2 
                                                                    ->
                                                                    let uu____4694
                                                                    =
                                                                    FStar_Syntax_Print.binder_to_string
                                                                    b2  in
                                                                    let uu____4696
                                                                    =
                                                                    FStar_Range.string_of_range
                                                                    r1  in
                                                                    FStar_Util.format3
                                                                    "implicit var for binder %s of %s:bind at %s"
                                                                    uu____4694
                                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                    uu____4696)
                                                                    r1  in
                                                                  (match uu____4641
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
                                                                    let uu____4733
                                                                    =
                                                                    let uu____4740
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b2
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    (uu____4740,
                                                                    t)  in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4733)
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
                                                                    let uu____4767
                                                                    =
                                                                    let uu____4768
                                                                    =
                                                                    let uu____4771
                                                                    =
                                                                    let uu____4772
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    uu____4772.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_Syntax_Subst.compress
                                                                    uu____4771
                                                                     in
                                                                    uu____4768.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____4767
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____4783,uu____4784::is)
                                                                    ->
                                                                    let uu____4826
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4826
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____4859
                                                                    ->
                                                                    let uu____4860
                                                                    =
                                                                    bind_t_shape_error
                                                                    "f's type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____4860
                                                                    r1  in
                                                                    FStar_List.fold_left2
                                                                    (fun g 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun f_i1 
                                                                    ->
                                                                    let uu____4876
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4876)
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
                                                                    let uu____4895
                                                                    =
                                                                    let uu____4896
                                                                    =
                                                                    let uu____4899
                                                                    =
                                                                    let uu____4900
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    g_b
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
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____4933
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____4933
                                                                    with
                                                                    | 
                                                                    (bs1,c3)
                                                                    ->
                                                                    let bs_subst
                                                                    =
                                                                    let uu____4943
                                                                    =
                                                                    let uu____4950
                                                                    =
                                                                    let uu____4951
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4951
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4972
                                                                    =
                                                                    let uu____4975
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4975
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4950,
                                                                    uu____4972)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4943
                                                                     in
                                                                    let c4 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c3  in
                                                                    let uu____4989
                                                                    =
                                                                    let uu____4990
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c4)  in
                                                                    uu____4990.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4989
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____4995,uu____4996::is)
                                                                    ->
                                                                    let uu____5038
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5038
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5071
                                                                    ->
                                                                    let uu____5072
                                                                    =
                                                                    bind_t_shape_error
                                                                    "g's type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5072
                                                                    r1))
                                                                    | 
                                                                    uu____5081
                                                                    ->
                                                                    let uu____5082
                                                                    =
                                                                    bind_t_shape_error
                                                                    "g's type is not an arrow"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5082
                                                                    r1  in
                                                                    let env_g
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [x_a]  in
                                                                    let uu____5104
                                                                    =
                                                                    FStar_List.fold_left2
                                                                    (fun g 
                                                                    ->
                                                                    fun i1 
                                                                    ->
                                                                    fun g_i1 
                                                                    ->
                                                                    let uu____5112
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5112)
                                                                    FStar_TypeChecker_Env.trivial_guard
                                                                    is2
                                                                    g_sort_is
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5104
                                                                    (FStar_TypeChecker_Env.close_guard
                                                                    env 
                                                                    [x_a])
                                                                     in
                                                                    let is =
                                                                    let uu____5128
                                                                    =
                                                                    let uu____5129
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    bind_ct.FStar_Syntax_Syntax.result_typ
                                                                     in
                                                                    uu____5129.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5128
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    (uu____5134,uu____5135::is)
                                                                    ->
                                                                    let uu____5177
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    is
                                                                    (FStar_List.map
                                                                    FStar_Pervasives_Native.fst)
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____5177
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1))
                                                                    | 
                                                                    uu____5210
                                                                    ->
                                                                    let uu____5211
                                                                    =
                                                                    bind_t_shape_error
                                                                    "return type is not a repr type"
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____5211
                                                                    r1  in
                                                                    let c =
                                                                    let uu____5221
                                                                    =
                                                                    let uu____5222
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
                                                                    uu____5222;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    uu____5221
                                                                     in
                                                                    ((
                                                                    let uu____5242
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "LayeredEffects")
                                                                     in
                                                                    if
                                                                    uu____5242
                                                                    then
                                                                    let uu____5247
                                                                    =
                                                                    FStar_Syntax_Print.comp_to_string
                                                                    c  in
                                                                    FStar_Util.print1
                                                                    "} c after bind: %s\n"
                                                                    uu____5247
                                                                    else ());
                                                                    (let uu____5252
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
                                                                    uu____5252))))))))))
                                         in
                                      let mk_bind c11 b1 c21 =
                                        let uu____5277 =
                                          lift_and_destruct env c11 c21  in
                                        match uu____5277 with
                                        | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2))
                                            ->
                                            let bs =
                                              match b1 with
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____5334 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      t1
                                                     in
                                                  [uu____5334]
                                              | FStar_Pervasives_Native.Some
                                                  x ->
                                                  let uu____5354 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____5354]
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
                                              let uu____5401 =
                                                FStar_Syntax_Syntax.as_arg
                                                  r11
                                                 in
                                              let uu____5410 =
                                                let uu____5421 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1
                                                   in
                                                let uu____5430 =
                                                  let uu____5441 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t2
                                                     in
                                                  let uu____5450 =
                                                    let uu____5461 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp1
                                                       in
                                                    let uu____5470 =
                                                      let uu____5481 =
                                                        let uu____5490 =
                                                          mk_lam wp2  in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu____5490
                                                         in
                                                      [uu____5481]  in
                                                    uu____5461 :: uu____5470
                                                     in
                                                  uu____5441 :: uu____5450
                                                   in
                                                uu____5421 :: uu____5430  in
                                              uu____5401 :: uu____5410  in
                                            let wp =
                                              let uu____5542 =
                                                let uu____5547 =
                                                  FStar_TypeChecker_Env.inst_effect_fun_with
                                                    [u_t1; u_t2] env md
                                                    md.FStar_Syntax_Syntax.bind_wp
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5547 wp_args
                                                 in
                                              uu____5542
                                                FStar_Pervasives_Native.None
                                                t2.FStar_Syntax_Syntax.pos
                                               in
                                            let uu____5548 =
                                              mk_comp md u_t2 t2 wp
                                                bind_flags
                                               in
                                            let uu____5549 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_c1 g_c2
                                               in
                                            (uu____5548, uu____5549)
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
                                        let uu____5576 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5576 with
                                        | (m,uu____5588,lift2) ->
                                            let c23 =
                                              let uu____5591 =
                                                lift_comp env c22 lift2  in
                                              FStar_Syntax_Syntax.mk_Comp
                                                uu____5591
                                               in
                                            let uu____5592 =
                                              destruct_comp c12  in
                                            (match uu____5592 with
                                             | (u1,t1,wp1) ->
                                                 let md_pure_or_ghost =
                                                   FStar_TypeChecker_Env.get_effect_decl
                                                     env
                                                     c12.FStar_Syntax_Syntax.effect_name
                                                    in
                                                 let vc1 =
                                                   let uu____5610 =
                                                     let uu____5615 =
                                                       let uu____5616 =
                                                         FStar_All.pipe_right
                                                           md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                           FStar_Util.must
                                                          in
                                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                                         [u1] env
                                                         md_pure_or_ghost
                                                         uu____5616
                                                        in
                                                     let uu____5619 =
                                                       let uu____5620 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           t1
                                                          in
                                                       let uu____5629 =
                                                         let uu____5640 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             wp1
                                                            in
                                                         [uu____5640]  in
                                                       uu____5620 ::
                                                         uu____5629
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____5615 uu____5619
                                                      in
                                                   uu____5610
                                                     FStar_Pervasives_Native.None
                                                     r1
                                                    in
                                                 let uu____5673 =
                                                   strengthen_comp env
                                                     FStar_Pervasives_Native.None
                                                     c23 vc1 bind_flags
                                                    in
                                                 let uu____5678 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 g_c2
                                                    in
                                                 (uu____5673, uu____5678))
                                         in
                                      let uu____5679 =
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
                                      if uu____5679
                                      then mk_layered_bind c1 b c2
                                      else
                                        (let c1_typ =
                                           FStar_TypeChecker_Env.unfold_effect_abbrev
                                             env c1
                                            in
                                         let uu____5691 =
                                           destruct_comp c1_typ  in
                                         match uu____5691 with
                                         | (u_res_t1,res_t1,uu____5704) ->
                                             let uu____5705 =
                                               (FStar_Option.isSome b) &&
                                                 (should_return env e1opt
                                                    lc11)
                                                in
                                             if uu____5705
                                             then
                                               let e1 =
                                                 FStar_Option.get e1opt  in
                                               let x = FStar_Option.get b  in
                                               let uu____5714 =
                                                 FStar_Syntax_Util.is_partial_return
                                                   c1
                                                  in
                                               (if uu____5714
                                                then
                                                  (debug1
                                                     (fun uu____5728  ->
                                                        let uu____5729 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5731 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case a): Substituting %s for %s"
                                                          uu____5729
                                                          uu____5731);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    mk_bind c1 b c21))
                                                else
                                                  (let uu____5739 =
                                                     ((FStar_Options.vcgen_optimize_bind_as_seq
                                                         ())
                                                        &&
                                                        (lcomp_has_trivial_postcondition
                                                           lc11))
                                                       &&
                                                       (let uu____5742 =
                                                          FStar_TypeChecker_Env.try_lookup_lid
                                                            env
                                                            FStar_Parser_Const.with_type_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____5742)
                                                      in
                                                   if uu____5739
                                                   then
                                                     let e1' =
                                                       let uu____5767 =
                                                         FStar_Options.vcgen_decorate_with_type
                                                           ()
                                                          in
                                                       if uu____5767
                                                       then
                                                         FStar_Syntax_Util.mk_with_type
                                                           u_res_t1 res_t1 e1
                                                       else e1  in
                                                     (debug1
                                                        (fun uu____5779  ->
                                                           let uu____5780 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1'
                                                              in
                                                           let uu____5782 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case b): Substituting %s for %s"
                                                             uu____5780
                                                             uu____5782);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1')] c2
                                                          in
                                                       mk_seq c1 b c21))
                                                   else
                                                     (debug1
                                                        (fun uu____5797  ->
                                                           let uu____5798 =
                                                             FStar_TypeChecker_Normalize.term_to_string
                                                               env e1
                                                              in
                                                           let uu____5800 =
                                                             FStar_Syntax_Print.bv_to_string
                                                               x
                                                              in
                                                           FStar_Util.print2
                                                             "(3) bind (case c): Adding equality %s = %s"
                                                             uu____5798
                                                             uu____5800);
                                                      (let c21 =
                                                         FStar_Syntax_Subst.subst_comp
                                                           [FStar_Syntax_Syntax.NT
                                                              (x, e1)] c2
                                                          in
                                                       let x_eq_e =
                                                         let uu____5807 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_Syntax_Util.mk_eq2
                                                           u_res_t1 res_t1 e1
                                                           uu____5807
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
      | uu____5825 -> g2
  
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
            (let uu____5849 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____5849)
           in
        let flags =
          if should_return1
          then
            let uu____5857 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____5857
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____5875 =
          let uu____5876 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5876 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____5889 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____5889
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____5897 =
                  let uu____5899 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____5899  in
                (if uu____5897
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___748_5908 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___748_5908.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___748_5908.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___748_5908.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____5909 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____5909, g_c)
                 else
                   (let uu____5912 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____5912, g_c)))
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
                   let uu____5923 =
                     let uu____5924 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____5924
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____5923
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____5927 =
                   let uu____5932 =
                     let uu____5933 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____5933
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____5932  in
                 match uu____5927 with
                 | (bind_c,g_bind) ->
                     let uu____5942 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____5943 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____5942, uu____5943))
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
            fun uu____5979  ->
              match uu____5979 with
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
                    let uu____5991 =
                      ((let uu____5995 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____5995) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____5991
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6013 =
        let uu____6014 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6014  in
      FStar_Syntax_Syntax.fvar uu____6013 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6084  ->
                 match uu____6084 with
                 | (uu____6098,eff_label,uu____6100,uu____6101) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6114 =
          let uu____6122 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6160  ->
                    match uu____6160 with
                    | (uu____6175,uu____6176,flags,uu____6178) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6195  ->
                                match uu___5_6195 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6198 -> false))))
             in
          if uu____6122
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6114 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6235 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6237 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6237
              then
                let uu____6244 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____6244, FStar_TypeChecker_Env.trivial_guard)
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6283 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6283 with
                   | (if_then_else1,uu____6293,uu____6294) ->
                       let uu____6295 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6296 =
                         let uu____6301 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6302 =
                           let uu____6303 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____6312 =
                             let uu____6323 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____6332 =
                               let uu____6343 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____6352 =
                                 let uu____6363 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____6363]  in
                               uu____6343 :: uu____6352  in
                             uu____6323 :: uu____6332  in
                           uu____6303 :: uu____6312  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6301 uu____6302
                          in
                       uu____6296 FStar_Pervasives_Native.None uu____6295
                    in
                 let default_case =
                   let post_k =
                     let uu____6416 =
                       let uu____6425 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6425]  in
                     let uu____6444 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6416 uu____6444  in
                   let kwp =
                     let uu____6450 =
                       let uu____6459 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6459]  in
                     let uu____6478 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6450 uu____6478  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6485 =
                       let uu____6486 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6486]  in
                     let uu____6505 =
                       let uu____6508 =
                         let uu____6515 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6515
                          in
                       let uu____6516 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6508 uu____6516  in
                     FStar_Syntax_Util.abs uu____6485 uu____6505
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
                   let uu____6540 =
                     should_not_inline_whole_match ||
                       (let uu____6543 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6543)
                      in
                   if uu____6540 then cthen true else cthen false  in
                 let uu____6550 =
                   FStar_List.fold_right
                     (fun uu____6596  ->
                        fun uu____6597  ->
                          match (uu____6596, uu____6597) with
                          | ((g,eff_label,uu____6639,cthen),(celse,g_comp))
                              ->
                              let uu____6673 =
                                let uu____6678 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____6678
                                 in
                              (match uu____6673 with
                               | (cthen1,gthen) ->
                                   let uu____6685 =
                                     lift_and_destruct env cthen1 celse  in
                                   (match uu____6685 with
                                    | ((md,uu____6715,uu____6716),(uu____6717,uu____6718,wp_then),
                                       (uu____6720,uu____6721,wp_else)) ->
                                        let uu____6741 =
                                          let uu____6742 =
                                            ifthenelse md res_t g wp_then
                                              wp_else
                                             in
                                          mk_comp md u_res_t res_t uu____6742
                                            []
                                           in
                                        let uu____6743 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_comp gthen
                                           in
                                        (uu____6741, uu____6743)))) lcases
                     (default_case, FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____6550 with
                 | (comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____6768::[] -> (comp, g_comp)
                      | uu____6811 ->
                          let comp1 =
                            FStar_TypeChecker_Env.comp_to_comp_typ env comp
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              comp1.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____6830 = destruct_comp comp1  in
                          (match uu____6830 with
                           | (uu____6841,uu____6842,wp) ->
                               let uu____6844 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   md.FStar_Syntax_Syntax.match_wps
                                  in
                               (match uu____6844 with
                                | (uu____6855,ite_wp,uu____6857) ->
                                    let wp1 =
                                      let uu____6861 =
                                        let uu____6866 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u_res_t] env md ite_wp
                                           in
                                        let uu____6867 =
                                          let uu____6868 =
                                            FStar_Syntax_Syntax.as_arg res_t
                                             in
                                          let uu____6877 =
                                            let uu____6888 =
                                              FStar_Syntax_Syntax.as_arg wp
                                               in
                                            [uu____6888]  in
                                          uu____6868 :: uu____6877  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____6866 uu____6867
                                         in
                                      uu____6861 FStar_Pervasives_Native.None
                                        wp.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6921 =
                                      mk_comp md u_res_t res_t wp1
                                        bind_cases_flags
                                       in
                                    (uu____6921, g_comp)))))
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
          let uu____6955 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6955 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____6971 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____6977 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____6971 uu____6977
              else
                (let uu____6986 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____6992 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____6986 uu____6992)
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
          let uu____7017 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____7017
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____7020 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____7020
        then u_res
        else
          (let is_total =
             let uu____7027 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____7027
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____7038 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____7038 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7041 =
                    let uu____7047 =
                      let uu____7049 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____7049
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____7047)
                     in
                  FStar_Errors.raise_error uu____7041
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
      let uu____7073 = destruct_comp ct  in
      match uu____7073 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7092 = FStar_TypeChecker_Env.get_range env  in
            let uu____7093 =
              let uu____7098 =
                let uu____7099 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7099
                 in
              let uu____7102 =
                let uu____7103 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7112 =
                  let uu____7123 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7123]  in
                uu____7103 :: uu____7112  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7098 uu____7102  in
            uu____7093 FStar_Pervasives_Native.None uu____7092  in
          let uu____7156 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7156)
  
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
               let uu____7197 =
                 let uu____7198 = FStar_Syntax_Subst.compress t2  in
                 uu____7198.FStar_Syntax_Syntax.n  in
               match uu____7197 with
               | FStar_Syntax_Syntax.Tm_type uu____7202 -> true
               | uu____7204 -> false  in
             let uu____7206 =
               let uu____7207 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____7207.FStar_Syntax_Syntax.n  in
             match uu____7206 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7215 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7225 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7225
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7228 =
                     let uu____7229 =
                       let uu____7230 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7230
                        in
                     (FStar_Pervasives_Native.None, uu____7229)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7228
                    in
                 let e1 =
                   let uu____7236 =
                     let uu____7241 =
                       let uu____7242 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7242]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7241  in
                   uu____7236 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7267 -> (e, lc))
  
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
          (let uu____7302 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7302
           then
             let uu____7305 = FStar_Syntax_Print.term_to_string e  in
             let uu____7307 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____7309 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7305 uu____7307 uu____7309
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7319 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____7319 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7344 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7370 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____7370, false)
             else
               (let uu____7380 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____7380, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7393) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____7405 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____7405
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___931_7421 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___931_7421.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___931_7421.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___931_7421.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____7428 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____7428 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____7444 =
                      let uu____7445 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____7445 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____7465 =
                            let uu____7467 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____7467 = FStar_Syntax_Util.Equal  in
                          if uu____7465
                          then
                            ((let uu____7474 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7474
                              then
                                let uu____7478 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____7480 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____7478 uu____7480
                              else ());
                             (let uu____7485 = set_result_typ1 c  in
                              (uu____7485, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____7492 ->
                                   true
                               | uu____7500 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____7509 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____7509
                                  in
                               let lc1 =
                                 let uu____7511 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____7512 =
                                   let uu____7513 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____7513)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____7511 uu____7512
                                  in
                               ((let uu____7517 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7517
                                 then
                                   let uu____7521 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____7523 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____7525 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____7527 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____7521 uu____7523 uu____7525
                                     uu____7527
                                 else ());
                                (let uu____7532 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____7532 with
                                 | (c1,g_lc) ->
                                     let uu____7543 = set_result_typ1 c1  in
                                     let uu____7544 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____7543, uu____7544)))
                             else
                               ((let uu____7548 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7548
                                 then
                                   let uu____7552 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____7554 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____7552 uu____7554
                                 else ());
                                (let uu____7559 = set_result_typ1 c  in
                                 (uu____7559, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___968_7563 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___968_7563.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___968_7563.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___968_7563.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____7573 =
                      let uu____7574 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____7574
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____7584 =
                           let uu____7585 = FStar_Syntax_Subst.compress f1
                              in
                           uu____7585.FStar_Syntax_Syntax.n  in
                         match uu____7584 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____7592,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____7594;
                                           FStar_Syntax_Syntax.vars =
                                             uu____7595;_},uu____7596)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___984_7622 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___984_7622.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___984_7622.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___984_7622.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____7623 ->
                             let uu____7624 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____7624 with
                              | (c,g_c) ->
                                  ((let uu____7636 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7636
                                    then
                                      let uu____7640 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____7642 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____7644 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____7646 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____7640 uu____7642 uu____7644
                                        uu____7646
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
                                        let uu____7659 =
                                          let uu____7664 =
                                            let uu____7665 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____7665]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____7664
                                           in
                                        uu____7659
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____7692 =
                                      let uu____7697 =
                                        FStar_All.pipe_left
                                          (fun _7718  ->
                                             FStar_Pervasives_Native.Some
                                               _7718)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____7719 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____7720 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____7721 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____7697
                                        uu____7719 e uu____7720 uu____7721
                                       in
                                    match uu____7692 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1002_7729 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1002_7729.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1002_7729.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____7731 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____7731
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____7734 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____7734 with
                                         | (c2,g_lc) ->
                                             ((let uu____7746 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____7746
                                               then
                                                 let uu____7750 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____7750
                                               else ());
                                              (let uu____7755 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____7755))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_7764  ->
                              match uu___6_7764 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____7767 -> []))
                       in
                    let lc1 =
                      let uu____7769 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____7769 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1018_7771 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1018_7771.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1018_7771.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1018_7771.FStar_TypeChecker_Common.implicits)
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
        let uu____7807 =
          let uu____7810 =
            let uu____7815 =
              let uu____7816 =
                let uu____7825 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7825  in
              [uu____7816]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7815  in
          uu____7810 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7807  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____7848 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7848
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7867 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7883 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7900 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7900
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7916)::(ens,uu____7918)::uu____7919 ->
                    let uu____7962 =
                      let uu____7965 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7965  in
                    let uu____7966 =
                      let uu____7967 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7967  in
                    (uu____7962, uu____7966)
                | uu____7970 ->
                    let uu____7981 =
                      let uu____7987 =
                        let uu____7989 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____7989
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____7987)
                       in
                    FStar_Errors.raise_error uu____7981
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8009)::uu____8010 ->
                    let uu____8037 =
                      let uu____8042 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8042
                       in
                    (match uu____8037 with
                     | (us_r,uu____8074) ->
                         let uu____8075 =
                           let uu____8080 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8080
                            in
                         (match uu____8075 with
                          | (us_e,uu____8112) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8115 =
                                  let uu____8116 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8116
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8115
                                  us_r
                                 in
                              let as_ens =
                                let uu____8118 =
                                  let uu____8119 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8119
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8118
                                  us_e
                                 in
                              let req =
                                let uu____8123 =
                                  let uu____8128 =
                                    let uu____8129 =
                                      let uu____8140 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8140]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8129
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8128
                                   in
                                uu____8123 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8180 =
                                  let uu____8185 =
                                    let uu____8186 =
                                      let uu____8197 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8197]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8186
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8185
                                   in
                                uu____8180 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8234 =
                                let uu____8237 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8237  in
                              let uu____8238 =
                                let uu____8239 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8239  in
                              (uu____8234, uu____8238)))
                | uu____8242 -> failwith "Impossible"))
  
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
      (let uu____8276 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8276
       then
         let uu____8281 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8283 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8281 uu____8283
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
        (let uu____8337 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8337
         then
           let uu____8342 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8344 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8342
             uu____8344
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8355 =
      let uu____8357 =
        let uu____8358 = FStar_Syntax_Subst.compress t  in
        uu____8358.FStar_Syntax_Syntax.n  in
      match uu____8357 with
      | FStar_Syntax_Syntax.Tm_app uu____8362 -> false
      | uu____8380 -> true  in
    if uu____8355
    then t
    else
      (let uu____8385 = FStar_Syntax_Util.head_and_args t  in
       match uu____8385 with
       | (head1,args) ->
           let uu____8428 =
             let uu____8430 =
               let uu____8431 = FStar_Syntax_Subst.compress head1  in
               uu____8431.FStar_Syntax_Syntax.n  in
             match uu____8430 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8436 -> false  in
           if uu____8428
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8468 ->
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
          ((let uu____8515 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____8515
            then
              let uu____8518 = FStar_Syntax_Print.term_to_string e  in
              let uu____8520 = FStar_Syntax_Print.term_to_string t  in
              let uu____8522 =
                let uu____8524 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____8524
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____8518 uu____8520 uu____8522
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____8537 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____8537 with
              | (formals,uu____8553) ->
                  let n_implicits =
                    let uu____8575 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____8653  ->
                              match uu____8653 with
                              | (uu____8661,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____8668 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____8668 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____8575 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____8793 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____8793 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____8807 =
                      let uu____8813 =
                        let uu____8815 = FStar_Util.string_of_int n_expected
                           in
                        let uu____8817 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____8819 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____8815 uu____8817 uu____8819
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____8813)
                       in
                    let uu____8823 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____8807 uu____8823
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_8841 =
              match uu___7_8841 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____8884 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____8884 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _9015,uu____9002) when
                           _9015 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____9048,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____9050))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9084 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9084 with
                            | (v1,uu____9125,g) ->
                                ((let uu____9140 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9140
                                  then
                                    let uu____9143 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9143
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9153 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9153 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9246 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9246))))
                       | (uu____9273,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9310 =
                             let uu____9323 =
                               let uu____9330 =
                                 let uu____9335 = FStar_Dyn.mkdyn env  in
                                 (uu____9335, tau)  in
                               FStar_Pervasives_Native.Some uu____9330  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9323
                              in
                           (match uu____9310 with
                            | (v1,uu____9368,g) ->
                                ((let uu____9383 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9383
                                  then
                                    let uu____9386 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9386
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9396 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9396 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9489 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9489))))
                       | (uu____9516,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____9564 =
                       let uu____9591 = inst_n_binders t1  in
                       aux [] uu____9591 bs1  in
                     (match uu____9564 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____9663) -> (e, torig, guard)
                           | (uu____9694,[]) when
                               let uu____9725 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____9725 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____9727 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____9755 ->
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
            | uu____9768 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9780 =
      let uu____9784 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9784
        (FStar_List.map
           (fun u  ->
              let uu____9796 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9796 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9780 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9824 = FStar_Util.set_is_empty x  in
      if uu____9824
      then []
      else
        (let s =
           let uu____9842 =
             let uu____9845 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9845  in
           FStar_All.pipe_right uu____9842 FStar_Util.set_elements  in
         (let uu____9861 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9861
          then
            let uu____9866 =
              let uu____9868 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9868  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9866
          else ());
         (let r =
            let uu____9877 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9877  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9916 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9916
                     then
                       let uu____9921 =
                         let uu____9923 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9923
                          in
                       let uu____9927 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9929 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9921 uu____9927 uu____9929
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
        let uu____9959 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9959 FStar_Util.set_elements  in
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
        | ([],uu____9998) -> generalized_univ_names
        | (uu____10005,[]) -> explicit_univ_names
        | uu____10012 ->
            let uu____10021 =
              let uu____10027 =
                let uu____10029 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____10029
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____10027)
               in
            FStar_Errors.raise_error uu____10021 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10051 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10051
       then
         let uu____10056 = FStar_Syntax_Print.term_to_string t  in
         let uu____10058 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10056 uu____10058
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10067 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10067
        then
          let uu____10072 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10072
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10081 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10081
         then
           let uu____10086 = FStar_Syntax_Print.term_to_string t  in
           let uu____10088 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10086 uu____10088
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
        let uu____10172 =
          let uu____10174 =
            FStar_Util.for_all
              (fun uu____10188  ->
                 match uu____10188 with
                 | (uu____10198,uu____10199,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10174  in
        if uu____10172
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10251 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10251
              then
                let uu____10254 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10254
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10261 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10261
               then
                 let uu____10264 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10264
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10282 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10282 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10316 =
             match uu____10316 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10353 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10353
                   then
                     let uu____10358 =
                       let uu____10360 =
                         let uu____10364 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10364
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10360
                         (FStar_String.concat ", ")
                        in
                     let uu____10412 =
                       let uu____10414 =
                         let uu____10418 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10418
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10431 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10433 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10431
                                   uu____10433))
                          in
                       FStar_All.pipe_right uu____10414
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10358
                       uu____10412
                   else ());
                  (let univs2 =
                     let uu____10447 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10459 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10459) univs1
                       uu____10447
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10466 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10466
                    then
                      let uu____10471 =
                        let uu____10473 =
                          let uu____10477 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10477
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10473
                          (FStar_String.concat ", ")
                         in
                      let uu____10525 =
                        let uu____10527 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10541 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10543 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10541
                                    uu____10543))
                           in
                        FStar_All.pipe_right uu____10527
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10471 uu____10525
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10564 =
             let uu____10581 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10581  in
           match uu____10564 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10671 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10671
                 then ()
                 else
                   (let uu____10676 = lec_hd  in
                    match uu____10676 with
                    | (lb1,uu____10684,uu____10685) ->
                        let uu____10686 = lec2  in
                        (match uu____10686 with
                         | (lb2,uu____10694,uu____10695) ->
                             let msg =
                               let uu____10698 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10700 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10698 uu____10700
                                in
                             let uu____10703 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10703))
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
                 let uu____10771 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10771
                 then ()
                 else
                   (let uu____10776 = lec_hd  in
                    match uu____10776 with
                    | (lb1,uu____10784,uu____10785) ->
                        let uu____10786 = lec2  in
                        (match uu____10786 with
                         | (lb2,uu____10794,uu____10795) ->
                             let msg =
                               let uu____10798 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10800 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10798 uu____10800
                                in
                             let uu____10803 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10803))
                  in
               let lecs1 =
                 let uu____10814 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10867 = univs_and_uvars_of_lec this_lec  in
                        match uu____10867 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10814 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10972 = lec_hd  in
                   match uu____10972 with
                   | (lbname,e,c) ->
                       let uu____10982 =
                         let uu____10988 =
                           let uu____10990 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10992 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10994 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10990 uu____10992 uu____10994
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10988)
                          in
                       let uu____10998 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10982 uu____10998
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____11017 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____11017 with
                         | FStar_Pervasives_Native.Some uu____11026 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____11034 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____11038 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____11038 with
                              | (bs,kres) ->
                                  ((let uu____11082 =
                                      let uu____11083 =
                                        let uu____11086 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11086
                                         in
                                      uu____11083.FStar_Syntax_Syntax.n  in
                                    match uu____11082 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11087
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11091 =
                                          let uu____11093 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11093  in
                                        if uu____11091
                                        then fail1 kres
                                        else ()
                                    | uu____11098 -> fail1 kres);
                                   (let a =
                                      let uu____11100 =
                                        let uu____11103 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11106  ->
                                             FStar_Pervasives_Native.Some
                                               _11106) uu____11103
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11100
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11114 ->
                                          let uu____11123 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11123
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
                      (fun uu____11226  ->
                         match uu____11226 with
                         | (lbname,e,c) ->
                             let uu____11272 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11333 ->
                                   let uu____11346 = (e, c)  in
                                   (match uu____11346 with
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
                                                (fun uu____11386  ->
                                                   match uu____11386 with
                                                   | (x,uu____11392) ->
                                                       let uu____11393 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11393)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11411 =
                                                let uu____11413 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11413
                                                 in
                                              if uu____11411
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
                                          let uu____11422 =
                                            let uu____11423 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11423.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11422 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11448 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11448 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11459 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11463 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11463, gen_tvars))
                                in
                             (match uu____11272 with
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
        (let uu____11610 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11610
         then
           let uu____11613 =
             let uu____11615 =
               FStar_List.map
                 (fun uu____11630  ->
                    match uu____11630 with
                    | (lb,uu____11639,uu____11640) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11615 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11613
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11666  ->
                match uu____11666 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11695 = gen env is_rec lecs  in
           match uu____11695 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11794  ->
                       match uu____11794 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11856 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11856
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11904  ->
                           match uu____11904 with
                           | (l,us,e,c,gvs) ->
                               let uu____11938 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11940 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11942 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11944 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11946 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11938 uu____11940 uu____11942
                                 uu____11944 uu____11946))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11991  ->
                match uu____11991 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____12035 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____12035, t, c, gvs)) univnames_lecs
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
              (let uu____12096 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12096 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12102 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12105  -> FStar_Pervasives_Native.Some _12105)
                     uu____12102)
             in
          let is_var e1 =
            let uu____12113 =
              let uu____12114 = FStar_Syntax_Subst.compress e1  in
              uu____12114.FStar_Syntax_Syntax.n  in
            match uu____12113 with
            | FStar_Syntax_Syntax.Tm_name uu____12118 -> true
            | uu____12120 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1474_12141 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1474_12141.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1474_12141.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12142 -> e2  in
          let env2 =
            let uu___1477_12144 = env1  in
            let uu____12145 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1477_12144.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1477_12144.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1477_12144.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1477_12144.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1477_12144.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1477_12144.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1477_12144.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1477_12144.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1477_12144.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1477_12144.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1477_12144.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1477_12144.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1477_12144.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1477_12144.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1477_12144.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1477_12144.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1477_12144.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12145;
              FStar_TypeChecker_Env.is_iface =
                (uu___1477_12144.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1477_12144.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1477_12144.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1477_12144.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1477_12144.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1477_12144.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1477_12144.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1477_12144.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1477_12144.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1477_12144.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1477_12144.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1477_12144.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1477_12144.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1477_12144.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1477_12144.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1477_12144.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1477_12144.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                (uu___1493_12204.FStar_TypeChecker_Env.synth_hook);
=======
                (uu___1486_12242.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1486_12242.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1470_12026.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1470_12026.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1477_12144.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1477_12144.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
              FStar_TypeChecker_Env.splice =
                (uu___1477_12144.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1477_12144.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1477_12144.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1477_12144.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1477_12144.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1477_12144.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1477_12144.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1477_12144.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12147 = check1 env2 t1 t2  in
          match uu____12147 with
          | FStar_Pervasives_Native.None  ->
              let uu____12154 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12160 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12154 uu____12160
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12167 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12167
                then
                  let uu____12172 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12172
                else ());
               (let uu____12178 = decorate e t2  in (uu____12178, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12206 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12206
         then
           let uu____12209 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12209
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12223 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____12223 with
         | (c,g_c) ->
             let uu____12235 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____12235
             then
               let uu____12243 =
                 let uu____12245 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____12245  in
               (uu____12243, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____12253 =
                    let uu____12254 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____12254
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____12253
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____12255 = check_trivial_precondition env c1  in
                match uu____12255 with
                | (ct,vc,g_pre) ->
                    ((let uu____12271 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____12271
                      then
                        let uu____12276 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____12276
                      else ());
                     (let uu____12281 =
                        let uu____12283 =
                          let uu____12284 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____12284  in
                        discharge uu____12283  in
                      let uu____12285 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____12281, uu____12285)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12319 =
        match uu___8_12319 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12329)::[] -> f fst1
        | uu____12354 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12366 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12366
          (fun _12367  -> FStar_TypeChecker_Common.NonTrivial _12367)
         in
      let op_or_e e =
        let uu____12378 =
          let uu____12379 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12379  in
        FStar_All.pipe_right uu____12378
          (fun _12382  -> FStar_TypeChecker_Common.NonTrivial _12382)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12389  -> FStar_TypeChecker_Common.NonTrivial _12389)
         in
      let op_or_t t =
        let uu____12400 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12400
          (fun _12403  -> FStar_TypeChecker_Common.NonTrivial _12403)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12410  -> FStar_TypeChecker_Common.NonTrivial _12410)
         in
      let short_op_ite uu___9_12416 =
        match uu___9_12416 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12426)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12453)::[] ->
            let uu____12494 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12494
              (fun _12495  -> FStar_TypeChecker_Common.NonTrivial _12495)
        | uu____12496 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12508 =
          let uu____12516 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12516)  in
        let uu____12524 =
          let uu____12534 =
            let uu____12542 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12542)  in
          let uu____12550 =
            let uu____12560 =
              let uu____12568 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12568)  in
            let uu____12576 =
              let uu____12586 =
                let uu____12594 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12594)  in
              let uu____12602 =
                let uu____12612 =
                  let uu____12620 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12620)  in
                [uu____12612; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12586 :: uu____12602  in
            uu____12560 :: uu____12576  in
          uu____12534 :: uu____12550  in
        uu____12508 :: uu____12524  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12682 =
            FStar_Util.find_map table
              (fun uu____12697  ->
                 match uu____12697 with
                 | (x,mk1) ->
                     let uu____12714 = FStar_Ident.lid_equals x lid  in
                     if uu____12714
                     then
                       let uu____12719 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12719
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12682 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12723 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12731 =
      let uu____12732 = FStar_Syntax_Util.un_uinst l  in
      uu____12732.FStar_Syntax_Syntax.n  in
    match uu____12731 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12737 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12773)::uu____12774 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12793 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12802,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12803))::uu____12804 -> bs
      | uu____12822 ->
          let uu____12823 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12823 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12827 =
                 let uu____12828 = FStar_Syntax_Subst.compress t  in
                 uu____12828.FStar_Syntax_Syntax.n  in
               (match uu____12827 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12832) ->
                    let uu____12853 =
                      FStar_Util.prefix_until
                        (fun uu___10_12893  ->
                           match uu___10_12893 with
                           | (uu____12901,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____12902)) ->
                               false
                           | uu____12907 -> true) bs'
                       in
                    (match uu____12853 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____12943,uu____12944) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____13016,uu____13017) ->
                         let uu____13090 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13110  ->
                                   match uu____13110 with
                                   | (x,uu____13119) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13090
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13168  ->
                                     match uu____13168 with
                                     | (x,i) ->
                                         let uu____13187 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13187, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13198 -> bs))
  
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
            let uu____13227 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13227
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
          let uu____13258 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13258
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
        (let uu____13301 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13301
         then
           ((let uu____13306 = FStar_Ident.text_of_lid lident  in
             d uu____13306);
            (let uu____13308 = FStar_Ident.text_of_lid lident  in
             let uu____13310 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13308 uu____13310))
         else ());
        (let fv =
           let uu____13316 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13316
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
         let uu____13328 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1634_13330 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1634_13330.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1634_13330.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1634_13330.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1634_13330.FStar_Syntax_Syntax.sigattrs)
           }), uu____13328))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13348 =
        match uu___11_13348 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13351 -> false  in
      let reducibility uu___12_13359 =
        match uu___12_13359 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13366 -> false  in
      let assumption uu___13_13374 =
        match uu___13_13374 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13378 -> false  in
      let reification uu___14_13386 =
        match uu___14_13386 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13389 -> true
        | uu____13391 -> false  in
      let inferred uu___15_13399 =
        match uu___15_13399 with
        | FStar_Syntax_Syntax.Discriminator uu____13401 -> true
        | FStar_Syntax_Syntax.Projector uu____13403 -> true
        | FStar_Syntax_Syntax.RecordType uu____13409 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13419 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13432 -> false  in
      let has_eq uu___16_13440 =
        match uu___16_13440 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13444 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____13523 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13530 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____13541 =
        let uu____13543 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_13549  ->
                  match uu___17_13549 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____13552 -> false))
           in
        FStar_All.pipe_right uu____13543 Prims.op_Negation  in
      if uu____13541
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____13573 =
            let uu____13579 =
              let uu____13581 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____13581 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____13579)  in
          FStar_Errors.raise_error uu____13573 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____13599 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____13607 =
            let uu____13609 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____13609  in
          if uu____13607 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____13619),uu____13620) ->
              ((let uu____13632 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____13632
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____13641 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____13641
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13652 ->
              let uu____13661 =
                let uu____13663 =
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
                Prims.op_Negation uu____13663  in
              if uu____13661 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13673 ->
              let uu____13680 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13680 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13688 ->
              let uu____13695 =
                let uu____13697 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13697  in
              if uu____13695 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13707 ->
              let uu____13708 =
                let uu____13710 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13710  in
              if uu____13708 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13720 ->
              let uu____13721 =
                let uu____13723 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13723  in
              if uu____13721 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13733 ->
              let uu____13746 =
                let uu____13748 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13748  in
              if uu____13746 then err'1 () else ()
          | uu____13758 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____13781 =
          let uu____13786 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____13786
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____13781
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____13805 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____13805
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____13823 =
                          let uu____13824 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13824.FStar_Syntax_Syntax.n  in
                        match uu____13823 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____13830 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____13856 =
          let uu____13857 = FStar_Syntax_Subst.compress t1  in
          uu____13857.FStar_Syntax_Syntax.n  in
        match uu____13856 with
        | FStar_Syntax_Syntax.Tm_type uu____13861 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____13864 ->
            let uu____13879 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13879 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____13912 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____13912
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____13918;
               FStar_Syntax_Syntax.index = uu____13919;
               FStar_Syntax_Syntax.sort = t2;_},uu____13921)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13930,uu____13931) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____13973::[]) ->
            let uu____14012 =
              let uu____14013 = FStar_Syntax_Util.un_uinst head1  in
              uu____14013.FStar_Syntax_Syntax.n  in
            (match uu____14012 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____14018 -> false)
        | uu____14020 -> false
      
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
        (let uu____14030 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____14030
         then
           let uu____14035 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____14035
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
              let uu____14082 =
                let uu____14083 = FStar_Syntax_Subst.compress signature  in
                uu____14083.FStar_Syntax_Syntax.n  in
              match uu____14082 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14087) when
                  (FStar_List.length bs) = (Prims.of_int (2)) ->
                  let uu____14116 = FStar_Syntax_Subst.open_binders bs  in
                  (match uu____14116 with
                   | (a,uu____14118)::(wp,uu____14120)::[] ->
                       FStar_All.pipe_right wp.FStar_Syntax_Syntax.sort
                         (FStar_Syntax_Subst.subst
                            [FStar_Syntax_Syntax.NT (a, a_tm)]))
              | uu____14149 ->
                  let uu____14150 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name signature
                     in
                  FStar_Errors.raise_error uu____14150 r
               in
            let uu____14156 =
              let uu____14169 =
                let uu____14171 = FStar_Range.string_of_range r  in
                FStar_Util.format2 "implicit for wp of %s at %s"
                  eff_name.FStar_Ident.str uu____14171
                 in
              new_implicit_var uu____14169 r env wp_sort  in
            match uu____14156 with
            | (wp_uvar,uu____14179,g_wp_uvar) ->
                let eff_c =
                  let uu____14194 =
                    let uu____14195 =
                      let uu____14206 =
                        FStar_All.pipe_right wp_uvar
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____14206]  in
                    {
                      FStar_Syntax_Syntax.comp_univs = [u];
                      FStar_Syntax_Syntax.effect_name = eff_name;
                      FStar_Syntax_Syntax.result_typ = a_tm;
                      FStar_Syntax_Syntax.effect_args = uu____14195;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____14194  in
                let uu____14239 =
                  let uu____14240 =
                    let uu____14247 =
                      let uu____14248 =
                        let uu____14263 =
                          let uu____14272 =
                            FStar_Syntax_Syntax.null_binder
                              FStar_Syntax_Syntax.t_unit
                             in
                          [uu____14272]  in
                        (uu____14263, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____14248  in
                    FStar_Syntax_Syntax.mk uu____14247  in
                  uu____14240 FStar_Pervasives_Native.None r  in
                (uu____14239, g_wp_uvar)
  
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
                  let uu____14351 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14351 r  in
                let uu____14361 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14361 with
                | (uu____14370,signature) ->
                    let uu____14372 =
                      let uu____14373 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14373.FStar_Syntax_Syntax.n  in
                    (match uu____14372 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14381) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14429 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____14444 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____14446 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____14444 eff_name.FStar_Ident.str
                                       uu____14446) r
                                 in
                              (match uu____14429 with
                               | (is,g) ->
                                   let repr =
                                     let uu____14460 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14460
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14469 =
                                     let uu____14470 =
                                       let uu____14475 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14475
                                        in
                                     uu____14470 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14469, g))
                          | uu____14484 -> fail1 signature)
                     | uu____14485 -> fail1 signature)
  
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
            let uu____14516 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____14516
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
              let uu____14561 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____14561 with
              | (uu____14566,sig_tm) ->
                  let fail1 t =
                    let uu____14574 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____14574 r  in
                  let uu____14580 =
                    let uu____14581 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____14581.FStar_Syntax_Syntax.n  in
                  (match uu____14580 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14585) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____14608)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____14630 -> fail1 sig_tm)
                   | uu____14631 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.mlift_comp_t)
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____14652 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____14652
           then
             let uu____14657 = FStar_Syntax_Print.comp_to_string c  in
             let uu____14659 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____14657 uu____14659
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____14689 =
               let uu____14690 =
                 let uu____14696 =
                   let uu____14698 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____14700 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____14698 uu____14700
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____14696)  in
               FStar_Errors.raise_error uu____14690 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____14712,uu____14713::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____14781 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____14786,c1) ->
                    let uu____14808 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____14808
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____14843 -> err ())
              in
           let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____14845 =
             let uu____14856 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____14857 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____14856, (ct.FStar_Syntax_Syntax.result_typ), uu____14857)
              in
           match uu____14845 with
           | (u,a,c_is) ->
               let uu____14905 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____14905 with
                | (uu____14914,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____14925 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____14927 = FStar_Ident.string_of_lid tgt  in
                      let uu____14929 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____14925 uu____14927 s uu____14929
                       in
                    let uu____14932 =
                      let uu____14965 =
                        let uu____14966 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____14966.FStar_Syntax_Syntax.n  in
                      match uu____14965 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____15030 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____15030 with
                           | (a_b::bs1,c2) ->
                               let uu____15090 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____15152 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____15090, uu____15152))
                      | uu____15179 ->
                          let uu____15180 =
                            let uu____15186 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____15186)
                             in
                          FStar_Errors.raise_error uu____15180 r
                       in
                    (match uu____14932 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____15304 =
                           let uu____15311 =
                             let uu____15312 =
                               let uu____15313 =
                                 let uu____15320 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____15320, a)  in
                               FStar_Syntax_Syntax.NT uu____15313  in
                             [uu____15312]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____15311
                             (fun b  ->
                                let uu____15337 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____15339 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____15341 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____15343 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____15337 uu____15339 uu____15341
                                  uu____15343) r
                            in
                         (match uu____15304 with
                          | (rest_bs_uvars,g) ->
                              let substs =
                                FStar_List.map2
                                  (fun b  ->
                                     fun t  ->
                                       let uu____15380 =
                                         let uu____15387 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____15387, t)  in
                                       FStar_Syntax_Syntax.NT uu____15380)
                                  (a_b :: rest_bs) (a :: rest_bs_uvars)
                                 in
                              let guard_f =
                                let f_sort =
                                  let uu____15406 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                      (FStar_Syntax_Subst.subst substs)
                                     in
                                  FStar_All.pipe_right uu____15406
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____15412 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  effect_args_from_repr f_sort uu____15412
                                   in
                                FStar_List.fold_left2
                                  (fun g1  ->
                                     fun i1  ->
                                       fun i2  ->
                                         let uu____15421 =
                                           FStar_TypeChecker_Rel.teq env i1
                                             i2
                                            in
                                         FStar_TypeChecker_Env.conj_guard g1
                                           uu____15421)
                                  FStar_TypeChecker_Env.trivial_guard c_is
                                  f_sort_is
                                 in
                              let is =
                                let uu____15425 =
                                  FStar_TypeChecker_Env.is_layered_effect env
                                    tgt
                                   in
                                effect_args_from_repr
                                  lift_ct.FStar_Syntax_Syntax.result_typ
                                  uu____15425
                                 in
                              let c1 =
                                let uu____15428 =
                                  let uu____15429 =
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      is
                                     in
                                  {
                                    FStar_Syntax_Syntax.comp_univs =
                                      (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                    FStar_Syntax_Syntax.effect_name = tgt;
                                    FStar_Syntax_Syntax.result_typ = a;
                                    FStar_Syntax_Syntax.effect_args =
                                      uu____15429;
                                    FStar_Syntax_Syntax.flags =
                                      (ct.FStar_Syntax_Syntax.flags)
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____15428  in
                              ((let uu____15449 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____15449
                                then
                                  let uu____15454 =
                                    FStar_Syntax_Print.comp_to_string c1  in
                                  FStar_Util.print1 "} Lifted comp: %s\n"
                                    uu____15454
                                else ());
                               (let uu____15459 =
                                  FStar_TypeChecker_Env.conj_guard g guard_f
                                   in
                                (c1, uu____15459)))))))
  