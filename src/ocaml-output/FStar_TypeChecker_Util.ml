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
            let uu____1398 =
              let uu____1399 =
                let uu____1410 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1410]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1399;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1398
  
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
          let uu____1494 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1494
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
      let uu____1510 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____1510
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____1513  ->
           let uu____1514 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____1514)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1522 =
      let uu____1523 = FStar_Syntax_Subst.compress t  in
      uu____1523.FStar_Syntax_Syntax.n  in
    match uu____1522 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1527 -> true
    | uu____1543 -> false
  
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
              let uu____1613 =
                let uu____1615 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1615  in
              if uu____1613
              then f
              else (let uu____1622 = reason1 ()  in label uu____1622 r f)
  
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
            let uu___243_1643 = g  in
            let uu____1644 =
              let uu____1645 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1645  in
            {
              FStar_TypeChecker_Env.guard_f = uu____1644;
              FStar_TypeChecker_Env.deferred =
                (uu___243_1643.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___243_1643.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___243_1643.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1666 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1666
        then c
        else
          (let uu____1671 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1671
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____1733 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____1733]  in
                       let us =
                         let uu____1755 =
                           let uu____1758 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____1758]  in
                         u_res :: uu____1755  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____1764 =
                         let uu____1769 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____1770 =
                           let uu____1771 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____1780 =
                             let uu____1791 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____1800 =
                               let uu____1811 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____1811]  in
                             uu____1791 :: uu____1800  in
                           uu____1771 :: uu____1780  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1769 uu____1770
                          in
                       uu____1764 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1853 = destruct_comp c1  in
              match uu____1853 with
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
          (fun uu____1889  ->
             let uu____1890 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____1890)
  
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
              ({ FStar_Syntax_Syntax.ppname = uu____1913;
                 FStar_Syntax_Syntax.index = uu____1914;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____1916;
                     FStar_Syntax_Syntax.vars = uu____1917;_};_},uu____1918)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____1926 -> c
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___0_1938  ->
            match uu___0_1938 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1941 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____1966 =
            let uu____1969 =
              FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____1969 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____1966
            (fun c  ->
               (let uu____2025 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2025) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2029 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2029)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2040 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2040 with
                | (head1,uu____2057) ->
                    let uu____2078 =
                      let uu____2079 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2079.FStar_Syntax_Syntax.n  in
                    (match uu____2078 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2084 =
                           let uu____2086 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2086
                            in
                         Prims.op_Negation uu____2084
                     | uu____2087 -> true)))
              &&
              (let uu____2090 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2090)
  
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
            let uu____2118 =
              let uu____2120 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2120  in
            if uu____2118
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2127 = FStar_Syntax_Util.is_unit t  in
               if uu____2127
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
                    let uu____2136 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2136
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2141 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2141 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2151 =
                             let uu____2152 =
                               let uu____2157 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2158 =
                                 let uu____2159 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2168 =
                                   let uu____2179 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2179]  in
                                 uu____2159 :: uu____2168  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2157
                                 uu____2158
                                in
                             uu____2152 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2151)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2213 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2213
           then
             let uu____2218 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2220 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2222 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2218 uu____2220 uu____2222
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
                let uu____2260 =
                  FStar_TypeChecker_Env.monad_leq env
                    FStar_Parser_Const.effect_PURE_lid
                    md.FStar_Syntax_Syntax.mname
                   in
                match uu____2260 with
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
              let uu____2266 =
                let uu____2271 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [FStar_Syntax_Syntax.U_zero; u_res_t] env md
                    md.FStar_Syntax_Syntax.bind_wp
                   in
                let uu____2272 =
                  let uu____2273 =
                    let uu____2282 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_range r))
                        FStar_Pervasives_Native.None r
                       in
                    FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2282
                     in
                  let uu____2291 =
                    let uu____2302 =
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2319 =
                      let uu____2330 = FStar_Syntax_Syntax.as_arg res_t  in
                      let uu____2339 =
                        let uu____2350 = FStar_Syntax_Syntax.as_arg wp11  in
                        let uu____2359 =
                          let uu____2370 =
                            let uu____2379 =
                              let uu____2380 =
                                let uu____2381 =
                                  FStar_Syntax_Syntax.null_binder
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                [uu____2381]  in
                              FStar_Syntax_Util.abs uu____2380 wp2
                                (FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Util.mk_residual_comp
                                      FStar_Parser_Const.effect_Tot_lid
                                      FStar_Pervasives_Native.None
                                      [FStar_Syntax_Syntax.TOTAL]))
                               in
                            FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                              uu____2379
                             in
                          [uu____2370]  in
                        uu____2350 :: uu____2359  in
                      uu____2330 :: uu____2339  in
                    uu____2302 :: uu____2319  in
                  uu____2273 :: uu____2291  in
                FStar_Syntax_Syntax.mk_Tm_app uu____2271 uu____2272  in
              uu____2266 FStar_Pervasives_Native.None
                wp2.FStar_Syntax_Syntax.pos
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____2470 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_2476  ->
              match uu___1_2476 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____2479 -> false))
       in
    if uu____2470
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_2491  ->
              match uu___2_2491 with
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
        let uu____2511 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2511
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____2517 = destruct_comp c1  in
           match uu____2517 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assume_wp =
                 let uu____2530 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assume_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____2530  in
               let pure_assume_wp1 =
                 let uu____2535 =
                   let uu____2540 =
                     let uu____2541 =
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula
                        in
                     [uu____2541]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____2540
                    in
                 uu____2535 FStar_Pervasives_Native.None r  in
               let w_wp =
                 lift_wp_and_bind_with env pure_assume_wp1 md u_res_t res_t
                   wp
                  in
               let uu____2575 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t w_wp uu____2575)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2599 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____2601 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____2601
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____2607 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____2607 weaken
  
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
               let uu____2656 = destruct_comp c1  in
               match uu____2656 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let pure_assert_wp =
                     let uu____2668 =
                       FStar_Syntax_Syntax.lid_as_fv
                         FStar_Parser_Const.pure_assert_wp_lid
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     FStar_Syntax_Syntax.fv_to_tm uu____2668  in
                   let pure_assert_wp1 =
                     let uu____2673 =
                       let uu____2678 =
                         let uu____2679 =
                           let uu____2688 = label_opt env reason r f  in
                           FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                             uu____2688
                            in
                         [uu____2679]  in
                       FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp
                         uu____2678
                        in
                     uu____2673 FStar_Pervasives_Native.None r  in
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
            let uu____2759 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____2759
            then (lc, g0)
            else
              (let flags =
                 let uu____2771 =
                   let uu____2779 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____2779
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____2771 with
                 | (maybe_trivial_post,flags) ->
                     let uu____2809 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___3_2817  ->
                               match uu___3_2817 with
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
                               | uu____2820 -> []))
                        in
                     FStar_List.append flags uu____2809
                  in
               let strengthen uu____2826 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____2832 = FStar_TypeChecker_Env.guard_form g01  in
                    match uu____2832 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____2835 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____2835
                          then
                            let uu____2839 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____2841 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____2839 uu____2841
                          else ());
                         strengthen_comp env reason c f flags))
                  in
               let uu____2846 =
                 let uu____2847 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____2847
                   lc.FStar_Syntax_Syntax.res_typ flags strengthen
                  in
               (uu____2846,
                 (let uu___416_2849 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___416_2849.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___416_2849.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___416_2849.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_2858  ->
            match uu___4_2858 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____2862 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____2891 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____2891
          then e
          else
            (let uu____2898 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____2901 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____2901)
                in
             if uu____2898
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
          fun uu____2954  ->
            match uu____2954 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____2974 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____2974 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____2987 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____2987
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____2997 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____2997
                       then
                         let uu____3002 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____3002
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____3009 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____3009
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____3018 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____3018
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____3025 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____3025
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
                        lc21.FStar_Syntax_Syntax.res_typ
                       in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11  in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21  in
                     debug1
                       (fun uu____3055  ->
                          let uu____3056 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____3058 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____3063 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____3056 uu____3058 uu____3063);
                     (let aux uu____3081 =
                        let uu____3082 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____3082
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____3113 ->
                              let uu____3114 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____3114
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____3146 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____3146
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____3191 =
                        let uu____3192 =
                          let uu____3194 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____3194  in
                        if uu____3192
                        then
                          let uu____3208 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____3208
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____3231 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____3231))
                        else
                          (let uu____3246 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____3246
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___482_3288 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___482_3288.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___482_3288.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____3289 =
                                 let uu____3295 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____3295, reason)  in
                               FStar_Util.Inl uu____3289  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____3331 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____3331
                                   (close1 x "c1 Tot")
                             | (uu____3345,FStar_Pervasives_Native.Some x) ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____3368,uu____3369) -> aux ()
                           else
                             (let uu____3384 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____3384
                              then
                                let uu____3397 =
                                  let uu____3403 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____3403, "both GTot")  in
                                FStar_Util.Inl uu____3397
                              else aux ()))
                         in
                      let uu____3414 = try_simplify ()  in
                      match uu____3414 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____3440  ->
                                let uu____3441 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____3441);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____3455  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____3477 = lift_and_destruct env c11 c21
                                 in
                              match uu____3477 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____3530 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____3530]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____3550 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____3550]
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
                                    let uu____3597 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____3606 =
                                      let uu____3617 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____3626 =
                                        let uu____3637 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____3646 =
                                          let uu____3657 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____3666 =
                                            let uu____3677 =
                                              let uu____3686 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____3686
                                               in
                                            [uu____3677]  in
                                          uu____3657 :: uu____3666  in
                                        uu____3637 :: uu____3646  in
                                      uu____3617 :: uu____3626  in
                                    uu____3597 :: uu____3606  in
                                  let wp =
                                    let uu____3738 =
                                      let uu____3743 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____3743 wp_args
                                       in
                                    uu____3738 FStar_Pervasives_Native.None
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
                              let uu____3766 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____3766 with
                              | (m,uu____3774,lift2) ->
                                  let c23 =
                                    let uu____3777 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____3777
                                     in
                                  let uu____3778 = destruct_comp c12  in
                                  (match uu____3778 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____3792 =
                                           let uu____3797 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____3798 =
                                             let uu____3799 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____3808 =
                                               let uu____3819 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____3819]  in
                                             uu____3799 :: uu____3808  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____3797 uu____3798
                                            in
                                         uu____3792
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
                            let uu____3857 = destruct_comp c1_typ  in
                            match uu____3857 with
                            | (u_res_t1,res_t1,uu____3866) ->
                                let uu____3867 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____3867
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____3872 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____3872
                                   then
                                     (debug1
                                        (fun uu____3882  ->
                                           let uu____3883 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____3885 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____3883 uu____3885);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____3893 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____3896 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____3896)
                                         in
                                      if uu____3893
                                      then
                                        let e1' =
                                          let uu____3917 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____3917
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____3929  ->
                                              let uu____3930 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____3932 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____3930 uu____3932);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____3947  ->
                                              let uu____3948 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____3950 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____3948 uu____3950);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____3957 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____3957
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
      | uu____3975 -> g2
  
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
            (let uu____3999 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____3999)
           in
        let flags =
          if should_return1
          then
            let uu____4007 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____4007
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____4023 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____4027 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____4027
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____4033 =
              let uu____4035 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____4035  in
            (if uu____4033
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___601_4042 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___601_4042.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___601_4042.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___601_4042.FStar_Syntax_Syntax.effect_args);
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
               let uu____4055 =
                 let uu____4056 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____4056
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4055
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____4059 =
               let uu____4060 =
                 let uu____4061 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____4061
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____4060  in
             FStar_Syntax_Util.comp_set_flags uu____4059 flags)
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
            fun uu____4099  ->
              match uu____4099 with
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
                    let uu____4111 =
                      ((let uu____4115 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____4115) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____4111
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____4133 =
        let uu____4134 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____4134  in
      FStar_Syntax_Syntax.fvar uu____4133 FStar_Syntax_Syntax.delta_constant
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
               fun uu____4204  ->
                 match uu____4204 with
                 | (uu____4218,eff_label,uu____4220,uu____4221) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____4234 =
          let uu____4242 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____4280  ->
                    match uu____4280 with
                    | (uu____4295,uu____4296,flags,uu____4298) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_4315  ->
                                match uu___5_4315 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____4318 -> false))))
             in
          if uu____4242
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____4234 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____4351 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____4353 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4353
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____4394 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____4395 =
                     let uu____4400 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____4401 =
                       let uu____4402 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____4411 =
                         let uu____4422 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____4431 =
                           let uu____4442 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____4451 =
                             let uu____4462 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____4462]  in
                           uu____4442 :: uu____4451  in
                         uu____4422 :: uu____4431  in
                       uu____4402 :: uu____4411  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____4400 uu____4401  in
                   uu____4395 FStar_Pervasives_Native.None uu____4394  in
                 let default_case =
                   let post_k =
                     let uu____4515 =
                       let uu____4524 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____4524]  in
                     let uu____4543 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____4515 uu____4543  in
                   let kwp =
                     let uu____4549 =
                       let uu____4558 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____4558]  in
                     let uu____4577 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____4549 uu____4577  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____4584 =
                       let uu____4585 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____4585]  in
                     let uu____4604 =
                       let uu____4607 =
                         let uu____4614 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____4614
                          in
                       let uu____4615 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____4607 uu____4615  in
                     FStar_Syntax_Util.abs uu____4584 uu____4604
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
                   let uu____4639 =
                     should_not_inline_whole_match ||
                       (let uu____4642 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____4642)
                      in
                   if uu____4639 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____4681  ->
                        fun celse  ->
                          match uu____4681 with
                          | (g,eff_label,uu____4698,cthen) ->
                              let uu____4712 =
                                let uu____4737 =
                                  let uu____4738 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____4738
                                   in
                                lift_and_destruct env uu____4737 celse  in
                              (match uu____4712 with
                               | ((md,uu____4740,uu____4741),(uu____4742,uu____4743,wp_then),
                                  (uu____4745,uu____4746,wp_else)) ->
                                   let uu____4766 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____4766 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____4781::[] -> comp
                 | uu____4824 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____4843 = destruct_comp comp1  in
                     (match uu____4843 with
                      | (uu____4850,uu____4851,wp) ->
                          let wp1 =
                            let uu____4856 =
                              let uu____4861 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____4862 =
                                let uu____4863 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____4872 =
                                  let uu____4883 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____4883]  in
                                uu____4863 :: uu____4872  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____4861
                                uu____4862
                               in
                            uu____4856 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos
                             in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags))
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
          let uu____4949 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____4949 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____4965 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____4971 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____4965 uu____4971
              else
                (let uu____4980 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____4986 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____4980 uu____4986)
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
          let uu____5011 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____5011
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____5014 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____5014
        then u_res
        else
          (let is_total =
             let uu____5021 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____5021
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____5032 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____5032 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5035 =
                    let uu____5041 =
                      let uu____5043 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____5043
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____5041)
                     in
                  FStar_Errors.raise_error uu____5035
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
      let uu____5067 = destruct_comp ct  in
      match uu____5067 with
      | (u_t,t,wp) ->
          let vc =
            let uu____5086 = FStar_TypeChecker_Env.get_range env  in
            let uu____5087 =
              let uu____5092 =
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  md.FStar_Syntax_Syntax.trivial
                 in
              let uu____5093 =
                let uu____5094 = FStar_Syntax_Syntax.as_arg t  in
                let uu____5103 =
                  let uu____5114 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____5114]  in
                uu____5094 :: uu____5103  in
              FStar_Syntax_Syntax.mk_Tm_app uu____5092 uu____5093  in
            uu____5087 FStar_Pervasives_Native.None uu____5086  in
          let uu____5147 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____5147)
  
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
               let uu____5188 =
                 let uu____5189 = FStar_Syntax_Subst.compress t2  in
                 uu____5189.FStar_Syntax_Syntax.n  in
               match uu____5188 with
               | FStar_Syntax_Syntax.Tm_type uu____5193 -> true
               | uu____5195 -> false  in
             let uu____5197 =
               let uu____5198 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____5198.FStar_Syntax_Syntax.n  in
             match uu____5197 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____5206 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____5216 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____5216
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____5219 =
                     let uu____5220 =
                       let uu____5221 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____5221
                        in
                     (FStar_Pervasives_Native.None, uu____5220)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____5219
                    in
                 let e1 =
                   let uu____5227 =
                     let uu____5232 =
                       let uu____5233 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____5233]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5232  in
                   uu____5227 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____5258 -> (e, lc))
  
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
          (let uu____5293 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____5293
           then
             let uu____5296 = FStar_Syntax_Print.term_to_string e  in
             let uu____5298 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____5300 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____5296 uu____5298 uu____5300
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____5310 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____5310 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____5335 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____5361 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____5361, false)
             else
               (let uu____5371 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____5371, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____5384) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____5396 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____5396
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___766_5412 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___766_5412.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___766_5412.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___766_5412.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____5419 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____5419 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____5431 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t  in
                      let uu____5442 =
                        let uu____5444 = FStar_Syntax_Util.eq_tm t res_t  in
                        uu____5444 = FStar_Syntax_Util.Equal  in
                      if uu____5442
                      then
                        ((let uu____5447 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5447
                          then
                            let uu____5451 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____5453 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____5451 uu____5453
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
                           | FStar_Syntax_Syntax.Tm_refine uu____5464 -> true
                           | uu____5472 -> false  in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t
                              in
                           let cret =
                             let uu____5477 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             return_value env (comp_univ_opt c) res_t
                               uu____5477
                              in
                           let lc1 =
                             let uu____5479 =
                               FStar_Syntax_Util.lcomp_of_comp c  in
                             let uu____5480 =
                               let uu____5481 =
                                 FStar_Syntax_Util.lcomp_of_comp cret  in
                               ((FStar_Pervasives_Native.Some x), uu____5481)
                                in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____5479
                               uu____5480
                              in
                           ((let uu____5485 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____5485
                             then
                               let uu____5489 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____5491 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               let uu____5493 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____5495 =
                                 FStar_Syntax_Print.lcomp_to_string lc1  in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____5489 uu____5491 uu____5493 uu____5495
                             else ());
                            (let uu____5500 =
                               FStar_Syntax_Syntax.lcomp_comp lc1  in
                             set_result_typ1 uu____5500))
                         else
                           ((let uu____5504 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____5504
                             then
                               let uu____5508 =
                                 FStar_Syntax_Print.term_to_string res_t  in
                               let uu____5510 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____5508 uu____5510
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
                      let uu___798_5518 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___798_5518.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___798_5518.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___798_5518.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____5524 =
                      let uu____5525 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____5525
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____5531 =
                           let uu____5532 = FStar_Syntax_Subst.compress f1
                              in
                           uu____5532.FStar_Syntax_Syntax.n  in
                         match uu____5531 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____5535,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____5537;
                                           FStar_Syntax_Syntax.vars =
                                             uu____5538;_},uu____5539)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___814_5565 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___814_5565.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___814_5565.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___814_5565.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____5566 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____5569 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____5569
                               then
                                 let uu____5573 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____5575 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____5577 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____5579 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____5573 uu____5575 uu____5577
                                   uu____5579
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
                                   let uu____5592 =
                                     let uu____5597 =
                                       let uu____5598 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____5598]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____5597
                                      in
                                   uu____5592 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____5625 =
                                 let uu____5630 =
                                   FStar_All.pipe_left
                                     (fun _5651  ->
                                        FStar_Pervasives_Native.Some _5651)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____5652 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____5653 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____5654 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____5630
                                   uu____5652 e uu____5653 uu____5654
                                  in
                               match uu____5625 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___830_5658 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___830_5658.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___830_5658.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____5660 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____5660
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____5665 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____5665
                                     then
                                       let uu____5669 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____5669
                                     else ());
                                    c2))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___6_5682  ->
                              match uu___6_5682 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____5685 -> []))
                       in
                    let lc1 =
                      let uu____5687 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____5687 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___844_5689 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___844_5689.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___844_5689.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___844_5689.FStar_TypeChecker_Env.implicits)
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
        let uu____5725 =
          let uu____5728 =
            let uu____5733 =
              let uu____5734 =
                let uu____5743 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____5743  in
              [uu____5734]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____5733  in
          uu____5728 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____5725  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____5766 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____5766
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____5785 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____5801 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____5818 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____5818
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____5834)::(ens,uu____5836)::uu____5837 ->
                    let uu____5880 =
                      let uu____5883 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____5883  in
                    let uu____5884 =
                      let uu____5885 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____5885  in
                    (uu____5880, uu____5884)
                | uu____5888 ->
                    let uu____5899 =
                      let uu____5905 =
                        let uu____5907 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____5907
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____5905)
                       in
                    FStar_Errors.raise_error uu____5899
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____5927)::uu____5928 ->
                    let uu____5955 =
                      let uu____5960 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____5960
                       in
                    (match uu____5955 with
                     | (us_r,uu____5992) ->
                         let uu____5993 =
                           let uu____5998 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____5998
                            in
                         (match uu____5993 with
                          | (us_e,uu____6030) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____6033 =
                                  let uu____6034 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____6034
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6033
                                  us_r
                                 in
                              let as_ens =
                                let uu____6036 =
                                  let uu____6037 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____6037
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6036
                                  us_e
                                 in
                              let req =
                                let uu____6041 =
                                  let uu____6046 =
                                    let uu____6047 =
                                      let uu____6058 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6058]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6047
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6046
                                   in
                                uu____6041 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____6098 =
                                  let uu____6103 =
                                    let uu____6104 =
                                      let uu____6115 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6115]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6104
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6103
                                   in
                                uu____6098 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____6152 =
                                let uu____6155 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____6155  in
                              let uu____6156 =
                                let uu____6157 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____6157  in
                              (uu____6152, uu____6156)))
                | uu____6160 -> failwith "Impossible"))
  
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
      (let uu____6194 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____6194
       then
         let uu____6199 = FStar_Syntax_Print.term_to_string tm  in
         let uu____6201 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6199 uu____6201
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
        (let uu____6255 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____6255
         then
           let uu____6260 = FStar_Syntax_Print.term_to_string tm  in
           let uu____6262 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6260
             uu____6262
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____6273 =
      let uu____6275 =
        let uu____6276 = FStar_Syntax_Subst.compress t  in
        uu____6276.FStar_Syntax_Syntax.n  in
      match uu____6275 with
      | FStar_Syntax_Syntax.Tm_app uu____6280 -> false
      | uu____6298 -> true  in
    if uu____6273
    then t
    else
      (let uu____6303 = FStar_Syntax_Util.head_and_args t  in
       match uu____6303 with
       | (head1,args) ->
           let uu____6346 =
             let uu____6348 =
               let uu____6349 = FStar_Syntax_Subst.compress head1  in
               uu____6349.FStar_Syntax_Syntax.n  in
             match uu____6348 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6354 -> false  in
           if uu____6346
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6386 ->
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
          ((let uu____6433 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____6433
            then
              let uu____6436 = FStar_Syntax_Print.term_to_string e  in
              let uu____6438 = FStar_Syntax_Print.term_to_string t  in
              let uu____6440 =
                let uu____6442 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____6442
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____6436 uu____6438 uu____6440
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____6455 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____6455 with
              | (formals,uu____6471) ->
                  let n_implicits =
                    let uu____6493 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____6571  ->
                              match uu____6571 with
                              | (uu____6579,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____6586 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____6586 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____6493 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____6711 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____6711 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____6725 =
                      let uu____6731 =
                        let uu____6733 = FStar_Util.string_of_int n_expected
                           in
                        let uu____6735 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____6737 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____6733 uu____6735 uu____6737
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____6731)
                       in
                    let uu____6741 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____6725 uu____6741
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_6759 =
              match uu___7_6759 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____6802 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____6802 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _6933,uu____6920) when
                           _6933 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____6966,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____6968))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____7002 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____7002 with
                            | (v1,uu____7043,g) ->
                                ((let uu____7058 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____7058
                                  then
                                    let uu____7061 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____7061
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____7071 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____7071 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____7164 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____7164))))
                       | (uu____7191,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____7228 =
                             let uu____7241 =
                               let uu____7248 =
                                 let uu____7253 = FStar_Dyn.mkdyn env  in
                                 (uu____7253, tau)  in
                               FStar_Pervasives_Native.Some uu____7248  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____7241
                              in
                           (match uu____7228 with
                            | (v1,uu____7286,g) ->
                                ((let uu____7301 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____7301
                                  then
                                    let uu____7304 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____7304
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____7314 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____7314 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____7407 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____7407))))
                       | (uu____7434,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____7482 =
                       let uu____7509 = inst_n_binders t1  in
                       aux [] uu____7509 bs1  in
                     (match uu____7482 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____7581) -> (e, torig, guard)
                           | (uu____7612,[]) when
                               let uu____7643 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____7643 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____7645 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____7673 ->
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
            | uu____7686 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____7698 =
      let uu____7702 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____7702
        (FStar_List.map
           (fun u  ->
              let uu____7714 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____7714 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____7698 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____7742 = FStar_Util.set_is_empty x  in
      if uu____7742
      then []
      else
        (let s =
           let uu____7760 =
             let uu____7763 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____7763  in
           FStar_All.pipe_right uu____7760 FStar_Util.set_elements  in
         (let uu____7779 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____7779
          then
            let uu____7784 =
              let uu____7786 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____7786  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7784
          else ());
         (let r =
            let uu____7795 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____7795  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____7834 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____7834
                     then
                       let uu____7839 =
                         let uu____7841 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7841
                          in
                       let uu____7845 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____7847 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7839 uu____7845 uu____7847
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
        let uu____7877 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____7877 FStar_Util.set_elements  in
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
        | ([],uu____7916) -> generalized_univ_names
        | (uu____7923,[]) -> explicit_univ_names
        | uu____7930 ->
            let uu____7939 =
              let uu____7945 =
                let uu____7947 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____7947
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____7945)
               in
            FStar_Errors.raise_error uu____7939 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____7969 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____7969
       then
         let uu____7974 = FStar_Syntax_Print.term_to_string t  in
         let uu____7976 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____7974 uu____7976
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____7985 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____7985
        then
          let uu____7990 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____7990
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____7999 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____7999
         then
           let uu____8004 = FStar_Syntax_Print.term_to_string t  in
           let uu____8006 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____8004 uu____8006
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
        let uu____8090 =
          let uu____8092 =
            FStar_Util.for_all
              (fun uu____8106  ->
                 match uu____8106 with
                 | (uu____8116,uu____8117,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____8092  in
        if uu____8090
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8169 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____8169
              then
                let uu____8172 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8172
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____8179 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____8179
               then
                 let uu____8182 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8182
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____8200 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____8200 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____8234 =
             match uu____8234 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____8271 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____8271
                   then
                     let uu____8276 =
                       let uu____8278 =
                         let uu____8282 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____8282
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____8278
                         (FStar_String.concat ", ")
                        in
                     let uu____8330 =
                       let uu____8332 =
                         let uu____8336 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____8336
                           (FStar_List.map
                              (fun u  ->
                                 let uu____8349 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____8351 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____8349
                                   uu____8351))
                          in
                       FStar_All.pipe_right uu____8332
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8276
                       uu____8330
                   else ());
                  (let univs2 =
                     let uu____8365 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____8377 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____8377) univs1
                       uu____8365
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____8384 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____8384
                    then
                      let uu____8389 =
                        let uu____8391 =
                          let uu____8395 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____8395
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____8391
                          (FStar_String.concat ", ")
                         in
                      let uu____8443 =
                        let uu____8445 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____8459 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____8461 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____8459
                                    uu____8461))
                           in
                        FStar_All.pipe_right uu____8445
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8389
                        uu____8443
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____8482 =
             let uu____8499 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____8499  in
           match uu____8482 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8589 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____8589
                 then ()
                 else
                   (let uu____8594 = lec_hd  in
                    match uu____8594 with
                    | (lb1,uu____8602,uu____8603) ->
                        let uu____8604 = lec2  in
                        (match uu____8604 with
                         | (lb2,uu____8612,uu____8613) ->
                             let msg =
                               let uu____8616 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____8618 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8616 uu____8618
                                in
                             let uu____8621 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____8621))
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
                 let uu____8689 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____8689
                 then ()
                 else
                   (let uu____8694 = lec_hd  in
                    match uu____8694 with
                    | (lb1,uu____8702,uu____8703) ->
                        let uu____8704 = lec2  in
                        (match uu____8704 with
                         | (lb2,uu____8712,uu____8713) ->
                             let msg =
                               let uu____8716 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____8718 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8716 uu____8718
                                in
                             let uu____8721 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____8721))
                  in
               let lecs1 =
                 let uu____8732 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____8785 = univs_and_uvars_of_lec this_lec  in
                        match uu____8785 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8732 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____8890 = lec_hd  in
                   match uu____8890 with
                   | (lbname,e,c) ->
                       let uu____8900 =
                         let uu____8906 =
                           let uu____8908 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____8910 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____8912 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____8908 uu____8910 uu____8912
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____8906)
                          in
                       let uu____8916 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____8900 uu____8916
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____8935 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____8935 with
                         | FStar_Pervasives_Native.Some uu____8944 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____8952 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____8956 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____8956 with
                              | (bs,kres) ->
                                  ((let uu____9000 =
                                      let uu____9001 =
                                        let uu____9004 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine uu____9004
                                         in
                                      uu____9001.FStar_Syntax_Syntax.n  in
                                    match uu____9000 with
                                    | FStar_Syntax_Syntax.Tm_type uu____9005
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____9009 =
                                          let uu____9011 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____9011  in
                                        if uu____9009 then fail1 kres else ()
                                    | uu____9016 -> fail1 kres);
                                   (let a =
                                      let uu____9018 =
                                        let uu____9021 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _9024  ->
                                             FStar_Pervasives_Native.Some
                                               _9024) uu____9021
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____9018
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____9032 ->
                                          let uu____9041 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs uu____9041
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
                      (fun uu____9144  ->
                         match uu____9144 with
                         | (lbname,e,c) ->
                             let uu____9190 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9251 ->
                                   let uu____9264 = (e, c)  in
                                   (match uu____9264 with
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
                                                (fun uu____9304  ->
                                                   match uu____9304 with
                                                   | (x,uu____9310) ->
                                                       let uu____9311 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9311)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9329 =
                                                let uu____9331 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9331
                                                 in
                                              if uu____9329
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
                                          let uu____9340 =
                                            let uu____9341 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____9341.FStar_Syntax_Syntax.n
                                             in
                                          match uu____9340 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9366 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____9366 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9377 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____9381 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____9381, gen_tvars))
                                in
                             (match uu____9190 with
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
        (let uu____9528 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____9528
         then
           let uu____9531 =
             let uu____9533 =
               FStar_List.map
                 (fun uu____9548  ->
                    match uu____9548 with
                    | (lb,uu____9557,uu____9558) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____9533 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____9531
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9584  ->
                match uu____9584 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____9613 = gen env is_rec lecs  in
           match uu____9613 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9712  ->
                       match uu____9712 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____9774 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____9774
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____9822  ->
                           match uu____9822 with
                           | (l,us,e,c,gvs) ->
                               let uu____9856 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____9858 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____9860 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____9862 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____9864 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____9856 uu____9858 uu____9860 uu____9862
                                 uu____9864))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____9909  ->
                match uu____9909 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____9953 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____9953, t, c, gvs)) univnames_lecs
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
              (let uu____10014 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____10014 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10020 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _10023  -> FStar_Pervasives_Native.Some _10023)
                     uu____10020)
             in
          let is_var e1 =
            let uu____10031 =
              let uu____10032 = FStar_Syntax_Subst.compress e1  in
              uu____10032.FStar_Syntax_Syntax.n  in
            match uu____10031 with
            | FStar_Syntax_Syntax.Tm_name uu____10036 -> true
            | uu____10038 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1300_10059 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1300_10059.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1300_10059.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10060 -> e2  in
          let env2 =
            let uu___1303_10062 = env1  in
            let uu____10063 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1303_10062.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1303_10062.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1303_10062.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1303_10062.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1303_10062.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1303_10062.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1303_10062.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1303_10062.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1303_10062.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1303_10062.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1303_10062.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1303_10062.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1303_10062.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1303_10062.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1303_10062.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1303_10062.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1303_10062.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10063;
              FStar_TypeChecker_Env.is_iface =
                (uu___1303_10062.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1303_10062.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1303_10062.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1303_10062.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1303_10062.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1303_10062.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1303_10062.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1303_10062.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1303_10062.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1303_10062.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1303_10062.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1303_10062.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1303_10062.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1303_10062.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1303_10062.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1303_10062.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1303_10062.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1303_10062.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1303_10062.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1303_10062.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1303_10062.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1303_10062.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1303_10062.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1303_10062.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1303_10062.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1303_10062.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____10065 = check1 env2 t1 t2  in
          match uu____10065 with
          | FStar_Pervasives_Native.None  ->
              let uu____10072 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____10078 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____10072 uu____10078
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10085 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10085
                then
                  let uu____10090 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10090
                else ());
               (let uu____10096 = decorate e t2  in (uu____10096, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____10124 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____10124
         then
           let uu____10127 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____10127
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____10141 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____10141
         then
           let uu____10149 = discharge g1  in
           let uu____10151 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____10149, uu____10151)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____10160 =
                let uu____10161 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                FStar_All.pipe_right uu____10161 FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____10160
                (FStar_TypeChecker_Normalize.normalize_comp steps env)
               in
            let uu____10162 = check_trivial_precondition env c1  in
            match uu____10162 with
            | (ct,vc,g2) ->
                ((let uu____10178 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____10178
                  then
                    let uu____10183 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____10183
                  else ());
                 (let uu____10188 = discharge g2  in
                  let uu____10190 =
                    FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp  in
                  (uu____10188, uu____10190)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_10224 =
        match uu___8_10224 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10234)::[] -> f fst1
        | uu____10259 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____10271 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____10271
          (fun _10272  -> FStar_TypeChecker_Common.NonTrivial _10272)
         in
      let op_or_e e =
        let uu____10283 =
          let uu____10284 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____10284  in
        FStar_All.pipe_right uu____10283
          (fun _10287  -> FStar_TypeChecker_Common.NonTrivial _10287)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _10294  -> FStar_TypeChecker_Common.NonTrivial _10294)
         in
      let op_or_t t =
        let uu____10305 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____10305
          (fun _10308  -> FStar_TypeChecker_Common.NonTrivial _10308)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _10315  -> FStar_TypeChecker_Common.NonTrivial _10315)
         in
      let short_op_ite uu___9_10321 =
        match uu___9_10321 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10331)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10358)::[] ->
            let uu____10399 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____10399
              (fun _10400  -> FStar_TypeChecker_Common.NonTrivial _10400)
        | uu____10401 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____10413 =
          let uu____10421 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____10421)  in
        let uu____10429 =
          let uu____10439 =
            let uu____10447 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____10447)  in
          let uu____10455 =
            let uu____10465 =
              let uu____10473 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____10473)  in
            let uu____10481 =
              let uu____10491 =
                let uu____10499 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____10499)  in
              let uu____10507 =
                let uu____10517 =
                  let uu____10525 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____10525)  in
                [uu____10517; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____10491 :: uu____10507  in
            uu____10465 :: uu____10481  in
          uu____10439 :: uu____10455  in
        uu____10413 :: uu____10429  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____10587 =
            FStar_Util.find_map table
              (fun uu____10602  ->
                 match uu____10602 with
                 | (x,mk1) ->
                     let uu____10619 = FStar_Ident.lid_equals x lid  in
                     if uu____10619
                     then
                       let uu____10624 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____10624
                     else FStar_Pervasives_Native.None)
             in
          (match uu____10587 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10628 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____10636 =
      let uu____10637 = FStar_Syntax_Util.un_uinst l  in
      uu____10637.FStar_Syntax_Syntax.n  in
    match uu____10636 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10642 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10678)::uu____10679 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10698 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____10707,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10708))::uu____10709 -> bs
      | uu____10727 ->
          let uu____10728 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____10728 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10732 =
                 let uu____10733 = FStar_Syntax_Subst.compress t  in
                 uu____10733.FStar_Syntax_Syntax.n  in
               (match uu____10732 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10737) ->
                    let uu____10758 =
                      FStar_Util.prefix_until
                        (fun uu___10_10798  ->
                           match uu___10_10798 with
                           | (uu____10806,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10807)) ->
                               false
                           | uu____10812 -> true) bs'
                       in
                    (match uu____10758 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10848,uu____10849) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10921,uu____10922) ->
                         let uu____10995 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11015  ->
                                   match uu____11015 with
                                   | (x,uu____11024) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____10995
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11073  ->
                                     match uu____11073 with
                                     | (x,i) ->
                                         let uu____11092 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____11092, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11103 -> bs))
  
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
            let uu____11132 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____11132
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
          let uu____11163 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____11163
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
        (let uu____11206 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____11206
         then
           ((let uu____11211 = FStar_Ident.text_of_lid lident  in
             d uu____11211);
            (let uu____11213 = FStar_Ident.text_of_lid lident  in
             let uu____11215 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____11213 uu____11215))
         else ());
        (let fv =
           let uu____11221 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11221
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
         let uu____11233 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1458_11235 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1458_11235.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1458_11235.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1458_11235.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1458_11235.FStar_Syntax_Syntax.sigattrs)
           }), uu____11233))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_11253 =
        match uu___11_11253 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11256 -> false  in
      let reducibility uu___12_11264 =
        match uu___12_11264 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11271 -> false  in
      let assumption uu___13_11279 =
        match uu___13_11279 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11283 -> false  in
      let reification uu___14_11291 =
        match uu___14_11291 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11294 -> true
        | uu____11296 -> false  in
      let inferred uu___15_11304 =
        match uu___15_11304 with
        | FStar_Syntax_Syntax.Discriminator uu____11306 -> true
        | FStar_Syntax_Syntax.Projector uu____11308 -> true
        | FStar_Syntax_Syntax.RecordType uu____11314 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11324 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11337 -> false  in
      let has_eq uu___16_11345 =
        match uu___16_11345 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11349 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____11428 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11435 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____11446 =
        let uu____11448 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_11454  ->
                  match uu___17_11454 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11457 -> false))
           in
        FStar_All.pipe_right uu____11448 Prims.op_Negation  in
      if uu____11446
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____11478 =
            let uu____11484 =
              let uu____11486 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11486 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11484)  in
          FStar_Errors.raise_error uu____11478 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____11504 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11512 =
            let uu____11514 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____11514  in
          if uu____11512 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11524),uu____11525) ->
              ((let uu____11537 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____11537
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11546 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____11546
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11557 ->
              let uu____11566 =
                let uu____11568 =
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
                Prims.op_Negation uu____11568  in
              if uu____11566 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11578 ->
              let uu____11585 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____11585 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11593 ->
              let uu____11600 =
                let uu____11602 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____11602  in
              if uu____11600 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11612 ->
              let uu____11613 =
                let uu____11615 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11615  in
              if uu____11613 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11625 ->
              let uu____11626 =
                let uu____11628 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11628  in
              if uu____11626 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11638 ->
              let uu____11651 =
                let uu____11653 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____11653  in
              if uu____11651 then err'1 () else ()
          | uu____11663 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____11686 =
          let uu____11691 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____11691
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____11686
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____11710 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____11710
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____11728 =
                          let uu____11729 = FStar_Syntax_Subst.compress t1
                             in
                          uu____11729.FStar_Syntax_Syntax.n  in
                        match uu____11728 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____11735 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____11761 =
          let uu____11762 = FStar_Syntax_Subst.compress t1  in
          uu____11762.FStar_Syntax_Syntax.n  in
        match uu____11761 with
        | FStar_Syntax_Syntax.Tm_type uu____11766 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____11769 ->
            let uu____11784 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____11784 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____11817 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____11817
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____11823;
               FStar_Syntax_Syntax.index = uu____11824;
               FStar_Syntax_Syntax.sort = t2;_},uu____11826)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____11835,uu____11836) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____11878::[]) ->
            let uu____11917 =
              let uu____11918 = FStar_Syntax_Util.un_uinst head1  in
              uu____11918.FStar_Syntax_Syntax.n  in
            (match uu____11917 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____11923 -> false)
        | uu____11925 -> false
      
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
        (let uu____11935 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____11935
         then
           let uu____11940 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____11940
         else ());
        res
       in aux g t
  