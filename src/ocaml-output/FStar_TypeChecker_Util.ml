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
  
let (destruct_wp_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  = fun c  -> FStar_Syntax_Util.destruct_comp c 
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____1075 =
          FStar_All.pipe_right
            (let uu___166_1077 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___166_1077.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___166_1077.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___166_1077.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___166_1077.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____1075
          (lift.FStar_TypeChecker_Env.mlift_wp env)
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1098 =
          let uu____1105 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1106 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1105 uu____1106  in
        match uu____1098 with | (m,uu____1108,uu____1109) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1126 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1126
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_TypeChecker_Common.eff_name
            c2.FStar_TypeChecker_Common.eff_name
  
let (lift_comps :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          Prims.bool ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun b_maybe_free_in_c2  ->
            let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
            let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
            let uu____1181 =
              FStar_TypeChecker_Env.join env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____1181 with
            | (m,lift1,lift2) ->
                let uu____1199 = lift_comp env c11 lift1  in
                (match uu____1199 with
                 | (c12,g1) ->
                     let uu____1214 =
                       if Prims.op_Negation b_maybe_free_in_c2
                       then lift_comp env c21 lift2
                       else
                         (let x_a =
                            match b with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Syntax.null_binder
                                  (FStar_Syntax_Util.comp_result c12)
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Syntax.mk_binder x
                             in
                          let env_x =
                            FStar_TypeChecker_Env.push_binders env [x_a]  in
                          let uu____1253 = lift_comp env_x c21 lift2  in
                          match uu____1253 with
                          | (c22,g2) ->
                              let uu____1264 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____1264))
                        in
                     (match uu____1214 with
                      | (c22,g2) ->
                          let uu____1287 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (m, c12, c22, uu____1287)))
  
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
            let uu____1348 =
              let uu____1349 =
                let uu____1360 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1360]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1349;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1348
  
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
          let uu____1444 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1444
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1456 =
      let uu____1457 = FStar_Syntax_Subst.compress t  in
      uu____1457.FStar_Syntax_Syntax.n  in
    match uu____1456 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1461 -> true
    | uu____1477 -> false
  
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
              let uu____1547 =
                let uu____1549 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1549  in
              if uu____1547
              then f
              else (let uu____1556 = reason1 ()  in label uu____1556 r f)
  
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
            let uu___243_1577 = g  in
            let uu____1578 =
              let uu____1579 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1579  in
            {
              FStar_TypeChecker_Common.guard_f = uu____1578;
              FStar_TypeChecker_Common.deferred =
                (uu___243_1577.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___243_1577.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___243_1577.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1600 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1600
        then c
        else
          (let uu____1605 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1605
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let uu____1646 =
                  FStar_Syntax_Util.get_match_with_close_wps
                    md.FStar_Syntax_Syntax.match_wps
                   in
                match uu____1646 with
                | (uu____1655,uu____1656,close1) ->
                    FStar_List.fold_right
                      (fun x  ->
                         fun wp  ->
                           let bs =
                             let uu____1679 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____1679]  in
                           let us =
                             let uu____1701 =
                               let uu____1704 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               [uu____1704]  in
                             u_res :: uu____1701  in
                           let wp1 =
                             FStar_Syntax_Util.abs bs wp
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None
                                     [FStar_Syntax_Syntax.TOTAL]))
                              in
                           let uu____1710 =
                             let uu____1715 =
                               FStar_TypeChecker_Env.inst_effect_fun_with us
                                 env md close1
                                in
                             let uu____1716 =
                               let uu____1717 =
                                 FStar_Syntax_Syntax.as_arg res_t  in
                               let uu____1726 =
                                 let uu____1737 =
                                   FStar_Syntax_Syntax.as_arg
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____1746 =
                                   let uu____1757 =
                                     FStar_Syntax_Syntax.as_arg wp1  in
                                   [uu____1757]  in
                                 uu____1737 :: uu____1746  in
                               uu____1717 :: uu____1726  in
                             FStar_Syntax_Syntax.mk_Tm_app uu____1715
                               uu____1716
                              in
                           uu____1710 FStar_Pervasives_Native.None
                             wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1799 = destruct_wp_comp c1  in
              match uu____1799 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_wp_lcomp :
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
          (FStar_TypeChecker_Common.apply_lcomp (close_wp_comp env bvs)
             (fun g  ->
                let uu____1839 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____1839
                  (close_guard_implicits env bs)))
  
let (close_wp_comp_if_refinement_t :
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
              ({ FStar_Syntax_Syntax.ppname = uu____1862;
                 FStar_Syntax_Syntax.index = uu____1863;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____1865;
                     FStar_Syntax_Syntax.vars = uu____1866;_};_},uu____1867)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_wp_comp env [x] c
          | uu____1875 -> c
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_1887  ->
            match uu___0_1887 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1890 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____1915 =
            let uu____1918 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____1918 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____1915
            (fun c  ->
               (let uu____1974 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____1974) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____1978 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____1978)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____1989 = FStar_Syntax_Util.head_and_args' e  in
                match uu____1989 with
                | (head1,uu____2006) ->
                    let uu____2027 =
                      let uu____2028 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2028.FStar_Syntax_Syntax.n  in
                    (match uu____2027 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2033 =
                           let uu____2035 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2035
                            in
                         Prims.op_Negation uu____2033
                     | uu____2036 -> true)))
              &&
              (let uu____2039 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2039)
  
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
            let uu____2067 =
              let uu____2069 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2069  in
            if uu____2067
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2076 = FStar_Syntax_Util.is_unit t  in
               if uu____2076
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
                    let uu____2085 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2085
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2090 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2090 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2100 =
                             let uu____2101 =
                               let uu____2106 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2107 =
                                 let uu____2108 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2117 =
                                   let uu____2128 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2128]  in
                                 uu____2108 :: uu____2117  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2106
                                 uu____2107
                                in
                             uu____2101 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2100)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2162 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2162
           then
             let uu____2167 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2169 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2171 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2167 uu____2169 uu____2171
           else ());
          c
  
let (mk_layered_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.comp_typ ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.comp_typ ->
            FStar_Syntax_Syntax.cflag Prims.list ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun m  ->
      fun ct1  ->
        fun b  ->
          fun ct2  ->
            fun flags  ->
              fun r1  ->
                (let uu____2229 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____2229
                 then
                   let uu____2234 =
                     let uu____2236 = FStar_Syntax_Syntax.mk_Comp ct1  in
                     FStar_Syntax_Print.comp_to_string uu____2236  in
                   let uu____2237 =
                     let uu____2239 = FStar_Syntax_Syntax.mk_Comp ct2  in
                     FStar_Syntax_Print.comp_to_string uu____2239  in
                   FStar_Util.print2 "Binding c1:%s and c2:%s {\n" uu____2234
                     uu____2237
                 else ());
                (let ed = FStar_TypeChecker_Env.get_effect_decl env m  in
                 let uu____2244 =
                   let uu____2255 =
                     FStar_List.hd ct1.FStar_Syntax_Syntax.comp_univs  in
                   let uu____2256 =
                     FStar_List.map FStar_Pervasives_Native.fst
                       ct1.FStar_Syntax_Syntax.effect_args
                      in
                   (uu____2255, (ct1.FStar_Syntax_Syntax.result_typ),
                     uu____2256)
                    in
                 match uu____2244 with
                 | (u1,t1,is1) ->
                     let uu____2290 =
                       let uu____2301 =
                         FStar_List.hd ct2.FStar_Syntax_Syntax.comp_univs  in
                       let uu____2302 =
                         FStar_List.map FStar_Pervasives_Native.fst
                           ct2.FStar_Syntax_Syntax.effect_args
                          in
                       (uu____2301, (ct2.FStar_Syntax_Syntax.result_typ),
                         uu____2302)
                        in
                     (match uu____2290 with
                      | (u2,t2,is2) ->
                          let uu____2336 =
                            FStar_TypeChecker_Env.inst_tscheme_with
                              ed.FStar_Syntax_Syntax.bind_wp [u1; u2]
                             in
                          (match uu____2336 with
                           | (uu____2345,bind_t) ->
                               let bind_t_shape_error s =
                                 let uu____2360 =
                                   let uu____2362 =
                                     FStar_Syntax_Print.term_to_string bind_t
                                      in
                                   FStar_Util.format2
                                     "bind %s does not have proper shape (reason:%s)"
                                     uu____2362 s
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____2360)
                                  in
                               let uu____2366 =
                                 let uu____2411 =
                                   let uu____2412 =
                                     FStar_Syntax_Subst.compress bind_t  in
                                   uu____2412.FStar_Syntax_Syntax.n  in
                                 match uu____2411 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____2488 =
                                       FStar_Syntax_Subst.open_comp bs c  in
                                     (match uu____2488 with
                                      | (a_b::b_b::bs1,c1) ->
                                          let uu____2573 =
                                            let uu____2600 =
                                              FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   (Prims.of_int (2))) bs1
                                               in
                                            FStar_All.pipe_right uu____2600
                                              (fun uu____2685  ->
                                                 match uu____2685 with
                                                 | (l1,l2) ->
                                                     let uu____2766 =
                                                       FStar_List.hd l2  in
                                                     let uu____2779 =
                                                       let uu____2786 =
                                                         FStar_List.tl l2  in
                                                       FStar_List.hd
                                                         uu____2786
                                                        in
                                                     (l1, uu____2766,
                                                       uu____2779))
                                             in
                                          (match uu____2573 with
                                           | (rest_bs,f_b,g_b) ->
                                               let uu____2914 =
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                   c1
                                                  in
                                               (a_b, b_b, rest_bs, f_b, g_b,
                                                 uu____2914)))
                                 | uu____2947 ->
                                     let uu____2948 =
                                       bind_t_shape_error
                                         "Either not an arrow or not enough binders"
                                        in
                                     FStar_Errors.raise_error uu____2948 r1
                                  in
                               (match uu____2366 with
                                | (a_b,b_b,rest_bs,f_b,g_b,bind_ct) ->
                                    let uu____3073 =
                                      let uu____3080 =
                                        let uu____3081 =
                                          let uu____3082 =
                                            let uu____3089 =
                                              FStar_All.pipe_right a_b
                                                FStar_Pervasives_Native.fst
                                               in
                                            (uu____3089, t1)  in
                                          FStar_Syntax_Syntax.NT uu____3082
                                           in
                                        let uu____3100 =
                                          let uu____3103 =
                                            let uu____3104 =
                                              let uu____3111 =
                                                FStar_All.pipe_right b_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____3111, t2)  in
                                            FStar_Syntax_Syntax.NT uu____3104
                                             in
                                          [uu____3103]  in
                                        uu____3081 :: uu____3100  in
                                      FStar_TypeChecker_Env.uvars_for_binders
                                        env rest_bs uu____3080
                                        (fun b1  ->
                                           let uu____3126 =
                                             FStar_Syntax_Print.binder_to_string
                                               b1
                                              in
                                           let uu____3128 =
                                             FStar_Range.string_of_range r1
                                              in
                                           FStar_Util.format3
                                             "implicit var for binder %s of %s:bind at %s"
                                             uu____3126
                                             (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             uu____3128) r1
                                       in
                                    (match uu____3073 with
                                     | (rest_bs_uvars,g_uvars) ->
                                         let subst1 =
                                           FStar_List.map2
                                             (fun b1  ->
                                                fun t  ->
                                                  let uu____3165 =
                                                    let uu____3172 =
                                                      FStar_All.pipe_right b1
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    (uu____3172, t)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3165) (a_b :: b_b
                                             :: rest_bs) (t1 :: t2 ::
                                             rest_bs_uvars)
                                            in
                                         let f_guard =
                                           let f_sort_is =
                                             let uu____3199 =
                                               let uu____3200 =
                                                 let uu____3203 =
                                                   let uu____3204 =
                                                     FStar_All.pipe_right f_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3204.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3203
                                                  in
                                               uu____3200.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3199 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____3215,uu____3216::is)
                                                 ->
                                                 let uu____3258 =
                                                   FStar_All.pipe_right is
                                                     (FStar_List.map
                                                        FStar_Pervasives_Native.fst)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3258
                                                   (FStar_List.map
                                                      (FStar_Syntax_Subst.subst
                                                         subst1))
                                             | uu____3291 ->
                                                 let uu____3292 =
                                                   bind_t_shape_error
                                                     "f's type is not a repr type"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3292 r1
                                              in
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun i1  ->
                                                  fun f_i1  ->
                                                    let uu____3308 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env i1 f_i1
                                                       in
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g uu____3308)
                                             FStar_TypeChecker_Env.trivial_guard
                                             is1 f_sort_is
                                            in
                                         let g_guard =
                                           let x_a =
                                             match b with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Syntax_Syntax.null_binder
                                                   ct1.FStar_Syntax_Syntax.result_typ
                                             | FStar_Pervasives_Native.Some x
                                                 ->
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x
                                              in
                                           let g_sort_is =
                                             let uu____3327 =
                                               let uu____3328 =
                                                 let uu____3331 =
                                                   let uu____3332 =
                                                     FStar_All.pipe_right g_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3332.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3331
                                                  in
                                               uu____3328.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3327 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs,c) ->
                                                 let uu____3365 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c
                                                    in
                                                 (match uu____3365 with
                                                  | (bs1,c1) ->
                                                      let bs_subst =
                                                        let uu____3375 =
                                                          let uu____3382 =
                                                            let uu____3383 =
                                                              FStar_List.hd
                                                                bs1
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3383
                                                              FStar_Pervasives_Native.fst
                                                             in
                                                          let uu____3404 =
                                                            let uu____3407 =
                                                              FStar_All.pipe_right
                                                                x_a
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3407
                                                              FStar_Syntax_Syntax.bv_to_name
                                                             in
                                                          (uu____3382,
                                                            uu____3404)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____3375
                                                         in
                                                      let c2 =
                                                        FStar_Syntax_Subst.subst_comp
                                                          [bs_subst] c1
                                                         in
                                                      let uu____3421 =
                                                        let uu____3422 =
                                                          FStar_Syntax_Subst.compress
                                                            (FStar_Syntax_Util.comp_result
                                                               c2)
                                                           in
                                                        uu____3422.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____3421 with
                                                       | FStar_Syntax_Syntax.Tm_app
                                                           (uu____3427,uu____3428::is)
                                                           ->
                                                           let uu____3470 =
                                                             FStar_All.pipe_right
                                                               is
                                                               (FStar_List.map
                                                                  FStar_Pervasives_Native.fst)
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____3470
                                                             (FStar_List.map
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1))
                                                       | uu____3503 ->
                                                           let uu____3504 =
                                                             bind_t_shape_error
                                                               "g's type is not a repr type"
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____3504 r1))
                                             | uu____3513 ->
                                                 let uu____3514 =
                                                   bind_t_shape_error
                                                     "g's type is not an arrow"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3514 r1
                                              in
                                           let env_g =
                                             FStar_TypeChecker_Env.push_binders
                                               env [x_a]
                                              in
                                           let uu____3536 =
                                             FStar_List.fold_left2
                                               (fun g  ->
                                                  fun i1  ->
                                                    fun g_i1  ->
                                                      let uu____3544 =
                                                        FStar_TypeChecker_Rel.teq
                                                          env_g i1 g_i1
                                                         in
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g uu____3544)
                                               FStar_TypeChecker_Env.trivial_guard
                                               is2 g_sort_is
                                              in
                                           FStar_All.pipe_right uu____3536
                                             (FStar_TypeChecker_Env.close_guard
                                                env [x_a])
                                            in
                                         let is =
                                           let uu____3560 =
                                             let uu____3561 =
                                               FStar_Syntax_Subst.compress
                                                 bind_ct.FStar_Syntax_Syntax.result_typ
                                                in
                                             uu____3561.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3560 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____3566,uu____3567::is) ->
                                               let uu____3609 =
                                                 FStar_All.pipe_right is
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3609
                                                 (FStar_List.map
                                                    (FStar_Syntax_Subst.subst
                                                       subst1))
                                           | uu____3642 ->
                                               let uu____3643 =
                                                 bind_t_shape_error
                                                   "return type is not a repr type"
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____3643 r1
                                            in
                                         let c =
                                           let uu____3653 =
                                             let uu____3654 =
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 is
                                                in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 =
                                                 (ct2.FStar_Syntax_Syntax.comp_univs);
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = t2;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____3654;
                                               FStar_Syntax_Syntax.flags =
                                                 flags
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____3653
                                            in
                                         ((let uu____3674 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffects")
                                              in
                                           if uu____3674
                                           then
                                             let uu____3679 =
                                               FStar_Syntax_Print.comp_to_string
                                                 c
                                                in
                                             FStar_Util.print1
                                               "} c after bind: %s\n"
                                               uu____3679
                                           else ());
                                          (let uu____3684 =
                                             FStar_TypeChecker_Env.conj_guards
                                               [g_uvars; f_guard; g_guard]
                                              in
                                           (c, uu____3684))))))))
  
let (mk_non_layered_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.comp_typ ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.comp_typ ->
            FStar_Syntax_Syntax.cflag Prims.list ->
              FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun m  ->
      fun ct1  ->
        fun b  ->
          fun ct2  ->
            fun flags  ->
              fun r1  ->
                let uu____3729 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____3755 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____3755 with
                  | (a,kwp) ->
                      let uu____3786 = destruct_wp_comp ct1  in
                      let uu____3793 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____3786, uu____3793)
                   in
                match uu____3729 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____3846 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____3846]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____3866 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3866]
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
                      let uu____3913 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____3922 =
                        let uu____3933 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____3942 =
                          let uu____3953 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____3962 =
                            let uu____3973 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____3982 =
                              let uu____3993 =
                                let uu____4002 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____4002  in
                              [uu____3993]  in
                            uu____3973 :: uu____3982  in
                          uu____3953 :: uu____3962  in
                        uu____3933 :: uu____3942  in
                      uu____3913 :: uu____3922  in
                    let wp =
                      let uu____4054 =
                        let uu____4059 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md
                            md.FStar_Syntax_Syntax.bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4059 wp_args  in
                      uu____4054 FStar_Pervasives_Native.None
                        t2.FStar_Syntax_Syntax.pos
                       in
                    mk_comp md u_t2 t2 wp flags
  
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
              let uu____4107 = lift_comps env c1 c2 b true  in
              match uu____4107 with
              | (m,c11,c21,g_lift) ->
                  let uu____4125 =
                    let uu____4130 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c11  in
                    let uu____4131 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c21  in
                    (uu____4130, uu____4131)  in
                  (match uu____4125 with
                   | (ct1,ct2) ->
                       let uu____4138 =
                         let uu____4143 =
                           FStar_TypeChecker_Env.is_layered_effect env m  in
                         if uu____4143
                         then mk_layered_bind env m ct1 b ct2 flags r1
                         else
                           (let uu____4152 =
                              mk_non_layered_bind env m ct1 b ct2 flags r1
                               in
                            (uu____4152, FStar_TypeChecker_Env.trivial_guard))
                          in
                       (match uu____4138 with
                        | (c,g_bind) ->
                            let uu____4159 =
                              FStar_TypeChecker_Env.conj_guard g_lift g_bind
                               in
                            (c, uu____4159)))
  
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
            let uu____4196 =
              FStar_TypeChecker_Env.monad_leq env
                FStar_Parser_Const.effect_PURE_lid
                ct.FStar_Syntax_Syntax.effect_name
               in
            match uu____4196 with
            | FStar_Pervasives_Native.Some edge -> edge
            | FStar_Pervasives_Native.None  ->
                failwith
                  (Prims.op_Hat
                     "Impossible! lift_wp_and_bind_with: did not find a lift from PURE to "
                     (ct.FStar_Syntax_Syntax.effect_name).FStar_Ident.str)
             in
          let pure_c =
            let uu____4202 =
              let uu____4203 =
                let uu____4214 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____4214]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4203;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4202  in
          let uu____4247 =
            (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
              env pure_c
             in
          match uu____4247 with
          | (m_c,g_lift) ->
              let uu____4258 =
                mk_bind env pure_c FStar_Pervasives_Native.None c flags r  in
              (match uu____4258 with
               | (bind_c,g_bind) ->
                   let uu____4269 =
                     FStar_TypeChecker_Env.conj_guard g_lift g_bind  in
                   (bind_c, uu____4269))
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____4282 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4288  ->
              match uu___1_4288 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4291 -> false))
       in
    if uu____4282
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4303  ->
              match uu___2_4303 with
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
        let uu____4331 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4331
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____4342 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____4342  in
           let pure_assume_wp1 =
             let uu____4347 = FStar_TypeChecker_Env.get_range env  in
             let uu____4348 =
               let uu____4353 =
                 let uu____4354 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____4354]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4353  in
             uu____4348 FStar_Pervasives_Native.None uu____4347  in
           let uu____4387 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           lift_wp_and_bind_with env pure_assume_wp1 c uu____4387)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4415 =
          let uu____4416 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____4416 with
          | (c,g_c) ->
              let uu____4427 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4427
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____4441 = weaken_comp env c f1  in
                     (match uu____4441 with
                      | (c1,g_w) ->
                          let uu____4452 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____4452)))
           in
        let uu____4453 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____4453 weaken
  
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
                 let uu____4510 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____4510  in
               let pure_assert_wp1 =
                 let uu____4515 =
                   let uu____4520 =
                     let uu____4521 =
                       let uu____4530 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____4530
                        in
                     [uu____4521]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____4520
                    in
                 uu____4515 FStar_Pervasives_Native.None r  in
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
            let uu____4600 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____4600
            then (lc, g0)
            else
              (let flags =
                 let uu____4612 =
                   let uu____4620 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____4620
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4612 with
                 | (maybe_trivial_post,flags) ->
                     let uu____4650 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_4658  ->
                               match uu___3_4658 with
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
                               | uu____4661 -> []))
                        in
                     FStar_List.append flags uu____4650
                  in
               let strengthen uu____4671 =
                 let uu____4672 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____4672 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____4691 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____4691 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____4698 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4698
                              then
                                let uu____4702 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____4704 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____4702 uu____4704
                              else ());
                             (let uu____4709 =
                                strengthen_comp env reason c f flags  in
                              match uu____4709 with
                              | (c1,g_s) ->
                                  let uu____4720 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____4720))))
                  in
               let uu____4721 =
                 let uu____4722 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____4722
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____4721,
                 (let uu___579_4724 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___579_4724.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___579_4724.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___579_4724.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_4733  ->
            match uu___4_4733 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4737 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____4766 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4766
          then e
          else
            (let uu____4773 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4776 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4776)
                in
             if uu____4773
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
          fun uu____4829  ->
            match uu____4829 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4849 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____4849 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____4862 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____4862
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____4872 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____4872
                       then
                         let uu____4877 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____4877
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____4884 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____4884
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____4893 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____4893
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____4900 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____4900
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____4916 =
                  let uu____4917 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____4917
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____4925 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____4925, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____4928 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____4928 with
                     | (c1,g_c1) ->
                         let uu____4939 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____4939 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____4959  ->
                                    let uu____4960 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____4962 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____4967 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____4960 uu____4962 uu____4967);
                               (let aux uu____4985 =
                                  let uu____4986 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____4986
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5017
                                        ->
                                        let uu____5018 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5018
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5050 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5050
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____5095 =
                                  let uu____5096 =
                                    let uu____5098 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____5098  in
                                  if uu____5096
                                  then
                                    let uu____5112 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____5112
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5135 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5135))
                                  else
                                    (let uu____5150 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____5150
                                     then
                                       let close1 x reason c =
                                         let uu____5191 =
                                           let uu____5193 =
                                             FStar_All.pipe_right c
                                               (FStar_TypeChecker_Env.unfold_effect_abbrev
                                                  env)
                                              in
                                           FStar_All.pipe_right uu____5193
                                             (fun ct  ->
                                                FStar_TypeChecker_Env.is_layered_effect
                                                  env
                                                  ct.FStar_Syntax_Syntax.effect_name)
                                            in
                                         if uu____5191
                                         then FStar_Util.Inl (c, reason)
                                         else
                                           (let x1 =
                                              let uu___651_5218 = x  in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___651_5218.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___651_5218.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (FStar_Syntax_Util.comp_result
                                                     c1)
                                              }  in
                                            let uu____5219 =
                                              let uu____5225 =
                                                close_wp_comp_if_refinement_t
                                                  env
                                                  x1.FStar_Syntax_Syntax.sort
                                                  x1 c
                                                 in
                                              (uu____5225, reason)  in
                                            FStar_Util.Inl uu____5219)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____5261 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____5261
                                             (close1 x "c1 Tot")
                                       | (uu____5275,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____5298,uu____5299) -> aux ()
                                     else
                                       (let uu____5314 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____5314
                                        then
                                          let uu____5327 =
                                            let uu____5333 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____5333, "both GTot")  in
                                          FStar_Util.Inl uu____5327
                                        else aux ()))
                                   in
                                let uu____5344 = try_simplify ()  in
                                match uu____5344 with
                                | FStar_Util.Inl (c,reason) ->
                                    (debug1
                                       (fun uu____5374  ->
                                          let uu____5375 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____5375);
                                     (let uu____5378 =
                                        FStar_TypeChecker_Env.conj_guard g_c1
                                          g_c2
                                         in
                                      (c, uu____5378)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____5390  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____5416 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____5416 with
                                        | (c,g_bind) ->
                                            let uu____5427 =
                                              let uu____5428 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5428 g_bind
                                               in
                                            (c, uu____5427)
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
                                        let uu____5455 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5455 with
                                        | (m,uu____5467,lift2) ->
                                            let uu____5469 =
                                              lift_comp env c22 lift2  in
                                            (match uu____5469 with
                                             | (c23,g2) ->
                                                 let uu____5480 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____5480 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let vc1 =
                                                        let uu____5498 =
                                                          let uu____5503 =
                                                            let uu____5504 =
                                                              FStar_All.pipe_right
                                                                md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                                FStar_Util.must
                                                               in
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              uu____5504
                                                             in
                                                          let uu____5507 =
                                                            let uu____5508 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5517 =
                                                              let uu____5528
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5528]
                                                               in
                                                            uu____5508 ::
                                                              uu____5517
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5503
                                                            uu____5507
                                                           in
                                                        uu____5498
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5561 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____5561 with
                                                       | (c,g_s) ->
                                                           let uu____5576 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____5576))))
                                         in
                                      let c1_typ =
                                        FStar_TypeChecker_Env.unfold_effect_abbrev
                                          env c1
                                         in
                                      let uu____5578 =
                                        let uu____5585 =
                                          FStar_List.hd
                                            c1_typ.FStar_Syntax_Syntax.comp_univs
                                           in
                                        (uu____5585,
                                          (c1_typ.FStar_Syntax_Syntax.result_typ))
                                         in
                                      match uu____5578 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____5598 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____5598
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____5607 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____5607
                                             then
                                               (debug1
                                                  (fun uu____5621  ->
                                                     let uu____5622 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____5624 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____5622 uu____5624);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____5632 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____5635 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____5635)
                                                   in
                                                if uu____5632
                                                then
                                                  let e1' =
                                                    let uu____5660 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____5660
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____5672  ->
                                                        let uu____5673 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____5675 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____5673
                                                          uu____5675);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____5690  ->
                                                        let uu____5691 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5693 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____5691
                                                          uu____5693);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____5700 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____5700
                                                       in
                                                    let uu____5701 =
                                                      let uu____5706 =
                                                        let uu____5707 =
                                                          let uu____5708 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____5708]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____5707
                                                         in
                                                      weaken_comp uu____5706
                                                        c21 x_eq_e
                                                       in
                                                    match uu____5701 with
                                                    | (c22,g_w) ->
                                                        let uu____5733 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____5733
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____5744 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____5744))))))
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
      | uu____5761 -> g2
  
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
            (let uu____5785 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____5785)
           in
        let flags =
          if should_return1
          then
            let uu____5793 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____5793
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____5811 =
          let uu____5812 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5812 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____5825 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____5825
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____5833 =
                  let uu____5835 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____5835  in
                (if uu____5833
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___762_5844 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___762_5844.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___762_5844.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___762_5844.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____5845 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____5845, g_c)
                 else
                   (let uu____5848 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____5848, g_c)))
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
                   let uu____5859 =
                     let uu____5860 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____5860
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____5859
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____5863 =
                   let uu____5868 =
                     let uu____5869 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____5869
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____5868  in
                 match uu____5863 with
                 | (bind_c,g_bind) ->
                     let uu____5878 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____5879 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____5878, uu____5879))
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
            fun uu____5915  ->
              match uu____5915 with
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
                    let uu____5927 =
                      ((let uu____5931 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____5931) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____5927
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____5949 =
        let uu____5950 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____5950  in
      FStar_Syntax_Syntax.fvar uu____5949 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6020  ->
                 match uu____6020 with
                 | (uu____6034,eff_label,uu____6036,uu____6037) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6050 =
          let uu____6058 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6096  ->
                    match uu____6096 with
                    | (uu____6111,uu____6112,flags,uu____6114) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_6131  ->
                                match uu___5_6131 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6134 -> false))))
             in
          if uu____6058
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6050 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6171 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6173 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6173
              then
                let uu____6180 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____6180, FStar_TypeChecker_Env.trivial_guard)
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6219 =
                     FStar_Syntax_Util.get_match_with_close_wps
                       md.FStar_Syntax_Syntax.match_wps
                      in
                   match uu____6219 with
                   | (if_then_else1,uu____6229,uu____6230) ->
                       let uu____6231 =
                         FStar_Range.union_ranges
                           wp_t.FStar_Syntax_Syntax.pos
                           wp_e.FStar_Syntax_Syntax.pos
                          in
                       let uu____6232 =
                         let uu____6237 =
                           FStar_TypeChecker_Env.inst_effect_fun_with
                             [u_res_t] env md if_then_else1
                            in
                         let uu____6238 =
                           let uu____6239 = FStar_Syntax_Syntax.as_arg res_t1
                              in
                           let uu____6248 =
                             let uu____6259 = FStar_Syntax_Syntax.as_arg g
                                in
                             let uu____6268 =
                               let uu____6279 =
                                 FStar_Syntax_Syntax.as_arg wp_t  in
                               let uu____6288 =
                                 let uu____6299 =
                                   FStar_Syntax_Syntax.as_arg wp_e  in
                                 [uu____6299]  in
                               uu____6279 :: uu____6288  in
                             uu____6259 :: uu____6268  in
                           uu____6239 :: uu____6248  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____6237 uu____6238
                          in
                       uu____6232 FStar_Pervasives_Native.None uu____6231
                    in
                 let default_case =
                   let post_k =
                     let uu____6352 =
                       let uu____6361 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6361]  in
                     let uu____6380 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6352 uu____6380  in
                   let kwp =
                     let uu____6386 =
                       let uu____6395 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6395]  in
                     let uu____6414 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6386 uu____6414  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6421 =
                       let uu____6422 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6422]  in
                     let uu____6441 =
                       let uu____6444 =
                         let uu____6451 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6451
                          in
                       let uu____6452 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6444 uu____6452  in
                     FStar_Syntax_Util.abs uu____6421 uu____6441
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
                   let uu____6476 =
                     should_not_inline_whole_match ||
                       (let uu____6479 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6479)
                      in
                   if uu____6476 then cthen true else cthen false  in
                 let uu____6486 =
                   FStar_List.fold_right
                     (fun uu____6527  ->
                        fun uu____6528  ->
                          match (uu____6527, uu____6528) with
                          | ((g,eff_label,uu____6570,cthen),(celse,g_comp))
                              ->
                              let uu____6604 =
                                let uu____6609 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____6609
                                 in
                              (match uu____6604 with
                               | (cthen1,gthen) ->
                                   let uu____6616 =
                                     let uu____6629 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____6629 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____6656 =
                                           let uu____6663 =
                                             FStar_All.pipe_right cthen2
                                               FStar_Syntax_Util.comp_to_comp_typ
                                              in
                                           FStar_All.pipe_right uu____6663
                                             destruct_wp_comp
                                            in
                                         (match uu____6656 with
                                          | (uu____6682,uu____6683,wp_then)
                                              ->
                                              let uu____6685 =
                                                let uu____6692 =
                                                  FStar_All.pipe_right celse1
                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                   in
                                                FStar_All.pipe_right
                                                  uu____6692 destruct_wp_comp
                                                 in
                                              (match uu____6685 with
                                               | (uu____6711,uu____6712,wp_else)
                                                   ->
                                                   (md, wp_then, wp_else,
                                                     g_lift)))
                                      in
                                   (match uu____6616 with
                                    | (md,wp_then,wp_else,g_lift) ->
                                        let uu____6734 =
                                          let uu____6735 =
                                            ifthenelse md res_t g wp_then
                                              wp_else
                                             in
                                          mk_comp md u_res_t res_t uu____6735
                                            []
                                           in
                                        let uu____6736 =
                                          let uu____6737 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_comp gthen
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____6737 g_lift
                                           in
                                        (uu____6734, uu____6736)))) lcases
                     (default_case, FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____6486 with
                 | (comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____6762::[] -> (comp, g_comp)
                      | uu____6805 ->
                          let comp1 =
                            FStar_TypeChecker_Env.comp_to_comp_typ env comp
                             in
                          let md =
                            FStar_TypeChecker_Env.get_effect_decl env
                              comp1.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____6824 = destruct_wp_comp comp1  in
                          (match uu____6824 with
                           | (uu____6835,uu____6836,wp) ->
                               let uu____6838 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   md.FStar_Syntax_Syntax.match_wps
                                  in
                               (match uu____6838 with
                                | (uu____6849,ite_wp,uu____6851) ->
                                    let wp1 =
                                      let uu____6855 =
                                        let uu____6860 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [u_res_t] env md ite_wp
                                           in
                                        let uu____6861 =
                                          let uu____6862 =
                                            FStar_Syntax_Syntax.as_arg res_t
                                             in
                                          let uu____6871 =
                                            let uu____6882 =
                                              FStar_Syntax_Syntax.as_arg wp
                                               in
                                            [uu____6882]  in
                                          uu____6862 :: uu____6871  in
                                        FStar_Syntax_Syntax.mk_Tm_app
                                          uu____6860 uu____6861
                                         in
                                      uu____6855 FStar_Pervasives_Native.None
                                        wp.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6915 =
                                      mk_comp md u_res_t res_t wp1
                                        bind_cases_flags
                                       in
                                    (uu____6915, g_comp)))))
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
          let uu____6949 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6949 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____6965 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____6971 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____6965 uu____6971
              else
                (let uu____6980 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____6986 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____6980 uu____6986)
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
          let uu____7011 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____7011
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____7014 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____7014
        then u_res
        else
          (let is_total =
             let uu____7021 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____7021
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____7032 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____7032 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7035 =
                    let uu____7041 =
                      let uu____7043 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____7043
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____7041)
                     in
                  FStar_Errors.raise_error uu____7035
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
      let uu____7067 = destruct_wp_comp ct  in
      match uu____7067 with
      | (u_t,t,wp) ->
          let vc =
            let uu____7086 = FStar_TypeChecker_Env.get_range env  in
            let uu____7087 =
              let uu____7092 =
                let uu____7093 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____7093
                 in
              let uu____7096 =
                let uu____7097 = FStar_Syntax_Syntax.as_arg t  in
                let uu____7106 =
                  let uu____7117 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____7117]  in
                uu____7097 :: uu____7106  in
              FStar_Syntax_Syntax.mk_Tm_app uu____7092 uu____7096  in
            uu____7087 FStar_Pervasives_Native.None uu____7086  in
          let uu____7150 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____7150)
  
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
               let uu____7191 =
                 let uu____7192 = FStar_Syntax_Subst.compress t2  in
                 uu____7192.FStar_Syntax_Syntax.n  in
               match uu____7191 with
               | FStar_Syntax_Syntax.Tm_type uu____7196 -> true
               | uu____7198 -> false  in
             let uu____7200 =
               let uu____7201 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____7201.FStar_Syntax_Syntax.n  in
             match uu____7200 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____7209 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____7219 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____7219
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____7222 =
                     let uu____7223 =
                       let uu____7224 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7224
                        in
                     (FStar_Pervasives_Native.None, uu____7223)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____7222
                    in
                 let e1 =
                   let uu____7230 =
                     let uu____7235 =
                       let uu____7236 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____7236]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7235  in
                   uu____7230 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____7261 -> (e, lc))
  
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
          (let uu____7296 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____7296
           then
             let uu____7299 = FStar_Syntax_Print.term_to_string e  in
             let uu____7301 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____7303 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____7299 uu____7301 uu____7303
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____7313 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____7313 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____7338 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____7364 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____7364, false)
             else
               (let uu____7374 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____7374, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____7387) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____7399 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____7399
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___951_7415 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___951_7415.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___951_7415.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___951_7415.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____7422 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____7422 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____7438 =
                      let uu____7439 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____7439 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____7459 =
                            let uu____7461 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____7461 = FStar_Syntax_Util.Equal  in
                          if uu____7459
                          then
                            ((let uu____7468 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7468
                              then
                                let uu____7472 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____7474 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____7472 uu____7474
                              else ());
                             (let uu____7479 = set_result_typ1 c  in
                              (uu____7479, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____7486 ->
                                   true
                               | uu____7494 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____7503 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____7503
                                  in
                               let lc1 =
                                 let uu____7505 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____7506 =
                                   let uu____7507 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____7507)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____7505 uu____7506
                                  in
                               ((let uu____7511 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7511
                                 then
                                   let uu____7515 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____7517 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____7519 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____7521 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____7515 uu____7517 uu____7519
                                     uu____7521
                                 else ());
                                (let uu____7526 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____7526 with
                                 | (c1,g_lc) ->
                                     let uu____7537 = set_result_typ1 c1  in
                                     let uu____7538 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____7537, uu____7538)))
                             else
                               ((let uu____7542 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____7542
                                 then
                                   let uu____7546 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____7548 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____7546 uu____7548
                                 else ());
                                (let uu____7553 = set_result_typ1 c  in
                                 (uu____7553, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___988_7557 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___988_7557.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___988_7557.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___988_7557.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____7567 =
                      let uu____7568 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____7568
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____7578 =
                           let uu____7579 = FStar_Syntax_Subst.compress f1
                              in
                           uu____7579.FStar_Syntax_Syntax.n  in
                         match uu____7578 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____7586,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____7588;
                                           FStar_Syntax_Syntax.vars =
                                             uu____7589;_},uu____7590)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1004_7616 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1004_7616.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1004_7616.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1004_7616.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____7617 ->
                             let uu____7618 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____7618 with
                              | (c,g_c) ->
                                  ((let uu____7630 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7630
                                    then
                                      let uu____7634 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____7636 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____7638 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____7640 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____7634 uu____7636 uu____7638
                                        uu____7640
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
                                        let uu____7653 =
                                          let uu____7658 =
                                            let uu____7659 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____7659]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____7658
                                           in
                                        uu____7653
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____7686 =
                                      let uu____7691 =
                                        FStar_All.pipe_left
                                          (fun _7712  ->
                                             FStar_Pervasives_Native.Some
                                               _7712)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____7713 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____7714 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____7715 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____7691
                                        uu____7713 e uu____7714 uu____7715
                                       in
                                    match uu____7686 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1022_7723 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1022_7723.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1022_7723.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____7725 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____7725
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____7728 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____7728 with
                                         | (c2,g_lc) ->
                                             ((let uu____7740 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____7740
                                               then
                                                 let uu____7744 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____7744
                                               else ());
                                              (let uu____7749 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____7749))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_7758  ->
                              match uu___6_7758 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____7761 -> []))
                       in
                    let lc1 =
                      let uu____7763 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____7763 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1038_7765 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1038_7765.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1038_7765.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1038_7765.FStar_TypeChecker_Common.implicits)
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
        let uu____7801 =
          let uu____7804 =
            let uu____7809 =
              let uu____7810 =
                let uu____7819 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7819  in
              [uu____7810]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7809  in
          uu____7804 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7801  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____7842 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7842
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7861 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7877 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7894 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7894
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7910)::(ens,uu____7912)::uu____7913 ->
                    let uu____7956 =
                      let uu____7959 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7959  in
                    let uu____7960 =
                      let uu____7961 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7961  in
                    (uu____7956, uu____7960)
                | uu____7964 ->
                    let uu____7975 =
                      let uu____7981 =
                        let uu____7983 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____7983
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____7981)
                       in
                    FStar_Errors.raise_error uu____7975
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8003)::uu____8004 ->
                    let uu____8031 =
                      let uu____8036 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8036
                       in
                    (match uu____8031 with
                     | (us_r,uu____8068) ->
                         let uu____8069 =
                           let uu____8074 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8074
                            in
                         (match uu____8069 with
                          | (us_e,uu____8106) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8109 =
                                  let uu____8110 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8110
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8109
                                  us_r
                                 in
                              let as_ens =
                                let uu____8112 =
                                  let uu____8113 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8113
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8112
                                  us_e
                                 in
                              let req =
                                let uu____8117 =
                                  let uu____8122 =
                                    let uu____8123 =
                                      let uu____8134 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8134]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8123
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8122
                                   in
                                uu____8117 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8174 =
                                  let uu____8179 =
                                    let uu____8180 =
                                      let uu____8191 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8191]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8180
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8179
                                   in
                                uu____8174 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8228 =
                                let uu____8231 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8231  in
                              let uu____8232 =
                                let uu____8233 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8233  in
                              (uu____8228, uu____8232)))
                | uu____8236 -> failwith "Impossible"))
  
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
      (let uu____8270 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8270
       then
         let uu____8275 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8277 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8275 uu____8277
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
        (let uu____8331 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8331
         then
           let uu____8336 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8338 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8336
             uu____8338
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8349 =
      let uu____8351 =
        let uu____8352 = FStar_Syntax_Subst.compress t  in
        uu____8352.FStar_Syntax_Syntax.n  in
      match uu____8351 with
      | FStar_Syntax_Syntax.Tm_app uu____8356 -> false
      | uu____8374 -> true  in
    if uu____8349
    then t
    else
      (let uu____8379 = FStar_Syntax_Util.head_and_args t  in
       match uu____8379 with
       | (head1,args) ->
           let uu____8422 =
             let uu____8424 =
               let uu____8425 = FStar_Syntax_Subst.compress head1  in
               uu____8425.FStar_Syntax_Syntax.n  in
             match uu____8424 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8430 -> false  in
           if uu____8422
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8462 ->
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
          ((let uu____8509 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____8509
            then
              let uu____8512 = FStar_Syntax_Print.term_to_string e  in
              let uu____8514 = FStar_Syntax_Print.term_to_string t  in
              let uu____8516 =
                let uu____8518 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____8518
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____8512 uu____8514 uu____8516
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____8531 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____8531 with
              | (formals,uu____8547) ->
                  let n_implicits =
                    let uu____8569 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____8647  ->
                              match uu____8647 with
                              | (uu____8655,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____8662 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____8662 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____8569 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____8787 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____8787 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____8801 =
                      let uu____8807 =
                        let uu____8809 = FStar_Util.string_of_int n_expected
                           in
                        let uu____8811 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____8813 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____8809 uu____8811 uu____8813
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____8807)
                       in
                    let uu____8817 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____8801 uu____8817
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_8835 =
              match uu___7_8835 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____8878 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____8878 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _9009,uu____8996) when
                           _9009 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____9042,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____9044))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9078 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____9078 with
                            | (v1,uu____9119,g) ->
                                ((let uu____9134 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9134
                                  then
                                    let uu____9137 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____9137
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9147 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9147 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9240 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9240))))
                       | (uu____9267,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____9304 =
                             let uu____9317 =
                               let uu____9324 =
                                 let uu____9329 = FStar_Dyn.mkdyn env  in
                                 (uu____9329, tau)  in
                               FStar_Pervasives_Native.Some uu____9324  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____9317
                              in
                           (match uu____9304 with
                            | (v1,uu____9362,g) ->
                                ((let uu____9377 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____9377
                                  then
                                    let uu____9380 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____9380
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____9390 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____9390 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____9483 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____9483))))
                       | (uu____9510,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____9558 =
                       let uu____9585 = inst_n_binders t1  in
                       aux [] uu____9585 bs1  in
                     (match uu____9558 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____9657) -> (e, torig, guard)
                           | (uu____9688,[]) when
                               let uu____9719 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____9719 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____9721 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____9749 ->
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
            | uu____9762 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9774 =
      let uu____9778 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9778
        (FStar_List.map
           (fun u  ->
              let uu____9790 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9790 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9774 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9818 = FStar_Util.set_is_empty x  in
      if uu____9818
      then []
      else
        (let s =
           let uu____9836 =
             let uu____9839 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9839  in
           FStar_All.pipe_right uu____9836 FStar_Util.set_elements  in
         (let uu____9855 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9855
          then
            let uu____9860 =
              let uu____9862 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9862  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9860
          else ());
         (let r =
            let uu____9871 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9871  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9910 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9910
                     then
                       let uu____9915 =
                         let uu____9917 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9917
                          in
                       let uu____9921 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9923 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9915 uu____9921 uu____9923
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
        let uu____9953 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9953 FStar_Util.set_elements  in
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
        | ([],uu____9992) -> generalized_univ_names
        | (uu____9999,[]) -> explicit_univ_names
        | uu____10006 ->
            let uu____10015 =
              let uu____10021 =
                let uu____10023 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____10023
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____10021)
               in
            FStar_Errors.raise_error uu____10015 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____10045 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____10045
       then
         let uu____10050 = FStar_Syntax_Print.term_to_string t  in
         let uu____10052 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____10050 uu____10052
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____10061 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____10061
        then
          let uu____10066 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____10066
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____10075 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____10075
         then
           let uu____10080 = FStar_Syntax_Print.term_to_string t  in
           let uu____10082 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____10080 uu____10082
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
        let uu____10166 =
          let uu____10168 =
            FStar_Util.for_all
              (fun uu____10182  ->
                 match uu____10182 with
                 | (uu____10192,uu____10193,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____10168  in
        if uu____10166
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____10245 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____10245
              then
                let uu____10248 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____10248
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____10255 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____10255
               then
                 let uu____10258 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____10258
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____10276 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____10276 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____10310 =
             match uu____10310 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____10347 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____10347
                   then
                     let uu____10352 =
                       let uu____10354 =
                         let uu____10358 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____10358
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____10354
                         (FStar_String.concat ", ")
                        in
                     let uu____10406 =
                       let uu____10408 =
                         let uu____10412 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10412
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10425 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10427 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10425
                                   uu____10427))
                          in
                       FStar_All.pipe_right uu____10408
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____10352
                       uu____10406
                   else ());
                  (let univs2 =
                     let uu____10441 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10453 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10453) univs1
                       uu____10441
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10460 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10460
                    then
                      let uu____10465 =
                        let uu____10467 =
                          let uu____10471 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10471
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10467
                          (FStar_String.concat ", ")
                         in
                      let uu____10519 =
                        let uu____10521 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10535 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10537 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10535
                                    uu____10537))
                           in
                        FStar_All.pipe_right uu____10521
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10465 uu____10519
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10558 =
             let uu____10575 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10575  in
           match uu____10558 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10665 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10665
                 then ()
                 else
                   (let uu____10670 = lec_hd  in
                    match uu____10670 with
                    | (lb1,uu____10678,uu____10679) ->
                        let uu____10680 = lec2  in
                        (match uu____10680 with
                         | (lb2,uu____10688,uu____10689) ->
                             let msg =
                               let uu____10692 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10694 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10692 uu____10694
                                in
                             let uu____10697 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10697))
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
                 let uu____10765 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10765
                 then ()
                 else
                   (let uu____10770 = lec_hd  in
                    match uu____10770 with
                    | (lb1,uu____10778,uu____10779) ->
                        let uu____10780 = lec2  in
                        (match uu____10780 with
                         | (lb2,uu____10788,uu____10789) ->
                             let msg =
                               let uu____10792 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10794 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10792 uu____10794
                                in
                             let uu____10797 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10797))
                  in
               let lecs1 =
                 let uu____10808 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10861 = univs_and_uvars_of_lec this_lec  in
                        match uu____10861 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10808 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10966 = lec_hd  in
                   match uu____10966 with
                   | (lbname,e,c) ->
                       let uu____10976 =
                         let uu____10982 =
                           let uu____10984 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10986 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10988 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10984 uu____10986 uu____10988
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10982)
                          in
                       let uu____10992 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10976 uu____10992
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____11011 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____11011 with
                         | FStar_Pervasives_Native.Some uu____11020 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____11028 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____11032 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____11032 with
                              | (bs,kres) ->
                                  ((let uu____11076 =
                                      let uu____11077 =
                                        let uu____11080 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____11080
                                         in
                                      uu____11077.FStar_Syntax_Syntax.n  in
                                    match uu____11076 with
                                    | FStar_Syntax_Syntax.Tm_type uu____11081
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____11085 =
                                          let uu____11087 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____11087  in
                                        if uu____11085
                                        then fail1 kres
                                        else ()
                                    | uu____11092 -> fail1 kres);
                                   (let a =
                                      let uu____11094 =
                                        let uu____11097 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _11100  ->
                                             FStar_Pervasives_Native.Some
                                               _11100) uu____11097
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____11094
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____11108 ->
                                          let uu____11117 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____11117
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
                      (fun uu____11220  ->
                         match uu____11220 with
                         | (lbname,e,c) ->
                             let uu____11266 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____11327 ->
                                   let uu____11340 = (e, c)  in
                                   (match uu____11340 with
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
                                                (fun uu____11380  ->
                                                   match uu____11380 with
                                                   | (x,uu____11386) ->
                                                       let uu____11387 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____11387)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11405 =
                                                let uu____11407 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11407
                                                 in
                                              if uu____11405
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
                                          let uu____11416 =
                                            let uu____11417 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11417.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11416 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11442 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11442 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11453 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11457 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11457, gen_tvars))
                                in
                             (match uu____11266 with
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
        (let uu____11604 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11604
         then
           let uu____11607 =
             let uu____11609 =
               FStar_List.map
                 (fun uu____11624  ->
                    match uu____11624 with
                    | (lb,uu____11633,uu____11634) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11609 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11607
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11660  ->
                match uu____11660 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11689 = gen env is_rec lecs  in
           match uu____11689 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11788  ->
                       match uu____11788 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11850 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11850
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11898  ->
                           match uu____11898 with
                           | (l,us,e,c,gvs) ->
                               let uu____11932 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11934 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11936 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11938 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11940 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11932 uu____11934 uu____11936
                                 uu____11938 uu____11940))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11985  ->
                match uu____11985 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____12029 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____12029, t, c, gvs)) univnames_lecs
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
              (let uu____12090 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____12090 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____12096 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _12099  -> FStar_Pervasives_Native.Some _12099)
                     uu____12096)
             in
          let is_var e1 =
            let uu____12107 =
              let uu____12108 = FStar_Syntax_Subst.compress e1  in
              uu____12108.FStar_Syntax_Syntax.n  in
            match uu____12107 with
            | FStar_Syntax_Syntax.Tm_name uu____12112 -> true
            | uu____12114 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1494_12135 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1494_12135.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1494_12135.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____12136 -> e2  in
          let env2 =
            let uu___1497_12138 = env1  in
            let uu____12139 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1497_12138.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1497_12138.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1497_12138.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1497_12138.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1497_12138.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1497_12138.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1497_12138.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1497_12138.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1497_12138.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1497_12138.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1497_12138.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1497_12138.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1497_12138.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1497_12138.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1497_12138.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1497_12138.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1497_12138.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____12139;
              FStar_TypeChecker_Env.is_iface =
                (uu___1497_12138.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1497_12138.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1497_12138.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1497_12138.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1497_12138.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1497_12138.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1497_12138.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1497_12138.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1497_12138.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1497_12138.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1497_12138.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1497_12138.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1497_12138.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1497_12138.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1497_12138.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1497_12138.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1497_12138.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1497_12138.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1497_12138.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1497_12138.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1497_12138.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1497_12138.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1497_12138.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1497_12138.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1497_12138.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1497_12138.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1497_12138.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____12141 = check1 env2 t1 t2  in
          match uu____12141 with
          | FStar_Pervasives_Native.None  ->
              let uu____12148 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____12154 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____12148 uu____12154
          | FStar_Pervasives_Native.Some g ->
              ((let uu____12161 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12161
                then
                  let uu____12166 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____12166
                else ());
               (let uu____12172 = decorate e t2  in (uu____12172, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____12200 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12200
         then
           let uu____12203 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____12203
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____12217 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____12217 with
         | (c,g_c) ->
             let uu____12229 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____12229
             then
               let uu____12237 =
                 let uu____12239 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____12239  in
               (uu____12237, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____12247 =
                    let uu____12248 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____12248
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____12247
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____12249 = check_trivial_precondition env c1  in
                match uu____12249 with
                | (ct,vc,g_pre) ->
                    ((let uu____12265 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____12265
                      then
                        let uu____12270 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____12270
                      else ());
                     (let uu____12275 =
                        let uu____12277 =
                          let uu____12278 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____12278  in
                        discharge uu____12277  in
                      let uu____12279 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____12275, uu____12279)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_12313 =
        match uu___8_12313 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____12323)::[] -> f fst1
        | uu____12348 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____12360 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____12360
          (fun _12361  -> FStar_TypeChecker_Common.NonTrivial _12361)
         in
      let op_or_e e =
        let uu____12372 =
          let uu____12373 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____12373  in
        FStar_All.pipe_right uu____12372
          (fun _12376  -> FStar_TypeChecker_Common.NonTrivial _12376)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _12383  -> FStar_TypeChecker_Common.NonTrivial _12383)
         in
      let op_or_t t =
        let uu____12394 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____12394
          (fun _12397  -> FStar_TypeChecker_Common.NonTrivial _12397)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _12404  -> FStar_TypeChecker_Common.NonTrivial _12404)
         in
      let short_op_ite uu___9_12410 =
        match uu___9_12410 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____12420)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____12447)::[] ->
            let uu____12488 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12488
              (fun _12489  -> FStar_TypeChecker_Common.NonTrivial _12489)
        | uu____12490 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12502 =
          let uu____12510 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12510)  in
        let uu____12518 =
          let uu____12528 =
            let uu____12536 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12536)  in
          let uu____12544 =
            let uu____12554 =
              let uu____12562 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12562)  in
            let uu____12570 =
              let uu____12580 =
                let uu____12588 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12588)  in
              let uu____12596 =
                let uu____12606 =
                  let uu____12614 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12614)  in
                [uu____12606; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12580 :: uu____12596  in
            uu____12554 :: uu____12570  in
          uu____12528 :: uu____12544  in
        uu____12502 :: uu____12518  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12676 =
            FStar_Util.find_map table
              (fun uu____12691  ->
                 match uu____12691 with
                 | (x,mk1) ->
                     let uu____12708 = FStar_Ident.lid_equals x lid  in
                     if uu____12708
                     then
                       let uu____12713 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12713
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12676 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12717 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12725 =
      let uu____12726 = FStar_Syntax_Util.un_uinst l  in
      uu____12726.FStar_Syntax_Syntax.n  in
    match uu____12725 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12731 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12767)::uu____12768 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12787 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12796,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12797))::uu____12798 -> bs
      | uu____12816 ->
          let uu____12817 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12817 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12821 =
                 let uu____12822 = FStar_Syntax_Subst.compress t  in
                 uu____12822.FStar_Syntax_Syntax.n  in
               (match uu____12821 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12826) ->
                    let uu____12847 =
                      FStar_Util.prefix_until
                        (fun uu___10_12887  ->
                           match uu___10_12887 with
                           | (uu____12895,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____12896)) ->
                               false
                           | uu____12901 -> true) bs'
                       in
                    (match uu____12847 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____12937,uu____12938) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____13010,uu____13011) ->
                         let uu____13084 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____13104  ->
                                   match uu____13104 with
                                   | (x,uu____13113) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____13084
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____13162  ->
                                     match uu____13162 with
                                     | (x,i) ->
                                         let uu____13181 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____13181, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____13192 -> bs))
  
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
            let uu____13221 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____13221
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
          let uu____13252 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____13252
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
        (let uu____13295 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13295
         then
           ((let uu____13300 = FStar_Ident.text_of_lid lident  in
             d uu____13300);
            (let uu____13302 = FStar_Ident.text_of_lid lident  in
             let uu____13304 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____13302 uu____13304))
         else ());
        (let fv =
           let uu____13310 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____13310
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
         let uu____13322 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1654_13324 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1654_13324.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1654_13324.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1654_13324.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1654_13324.FStar_Syntax_Syntax.sigattrs)
           }), uu____13322))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_13342 =
        match uu___11_13342 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13345 -> false  in
      let reducibility uu___12_13353 =
        match uu___12_13353 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____13360 -> false  in
      let assumption uu___13_13368 =
        match uu___13_13368 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____13372 -> false  in
      let reification uu___14_13380 =
        match uu___14_13380 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____13383 -> true
        | uu____13385 -> false  in
      let inferred uu___15_13393 =
        match uu___15_13393 with
        | FStar_Syntax_Syntax.Discriminator uu____13395 -> true
        | FStar_Syntax_Syntax.Projector uu____13397 -> true
        | FStar_Syntax_Syntax.RecordType uu____13403 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____13413 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____13426 -> false  in
      let has_eq uu___16_13434 =
        match uu___16_13434 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____13438 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____13517 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____13524 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____13535 =
        let uu____13537 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_13543  ->
                  match uu___17_13543 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____13546 -> false))
           in
        FStar_All.pipe_right uu____13537 Prims.op_Negation  in
      if uu____13535
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____13567 =
            let uu____13573 =
              let uu____13575 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____13575 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____13573)  in
          FStar_Errors.raise_error uu____13567 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____13593 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____13601 =
            let uu____13603 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____13603  in
          if uu____13601 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____13613),uu____13614) ->
              ((let uu____13626 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____13626
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____13635 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____13635
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13646 ->
              let uu____13655 =
                let uu____13657 =
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
                Prims.op_Negation uu____13657  in
              if uu____13655 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13667 ->
              let uu____13674 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13674 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13682 ->
              let uu____13689 =
                let uu____13691 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13691  in
              if uu____13689 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13701 ->
              let uu____13702 =
                let uu____13704 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13704  in
              if uu____13702 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13714 ->
              let uu____13715 =
                let uu____13717 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13717  in
              if uu____13715 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13727 ->
              let uu____13740 =
                let uu____13742 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13742  in
              if uu____13740 then err'1 () else ()
          | uu____13752 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____13775 =
          let uu____13780 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____13780
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____13775
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____13799 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____13799
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____13817 =
                          let uu____13818 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13818.FStar_Syntax_Syntax.n  in
                        match uu____13817 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____13824 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____13850 =
          let uu____13851 = FStar_Syntax_Subst.compress t1  in
          uu____13851.FStar_Syntax_Syntax.n  in
        match uu____13850 with
        | FStar_Syntax_Syntax.Tm_type uu____13855 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____13858 ->
            let uu____13873 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13873 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____13906 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____13906
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____13912;
               FStar_Syntax_Syntax.index = uu____13913;
               FStar_Syntax_Syntax.sort = t2;_},uu____13915)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13924,uu____13925) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____13967::[]) ->
            let uu____14006 =
              let uu____14007 = FStar_Syntax_Util.un_uinst head1  in
              uu____14007.FStar_Syntax_Syntax.n  in
            (match uu____14006 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____14012 -> false)
        | uu____14014 -> false
      
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
        (let uu____14024 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____14024
         then
           let uu____14029 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____14029
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
              let uu____14076 =
                let uu____14077 = FStar_Syntax_Subst.compress signature  in
                uu____14077.FStar_Syntax_Syntax.n  in
              match uu____14076 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14081) when
                  (FStar_List.length bs) = (Prims.of_int (2)) ->
                  let uu____14110 = FStar_Syntax_Subst.open_binders bs  in
                  (match uu____14110 with
                   | (a,uu____14112)::(wp,uu____14114)::[] ->
                       FStar_All.pipe_right wp.FStar_Syntax_Syntax.sort
                         (FStar_Syntax_Subst.subst
                            [FStar_Syntax_Syntax.NT (a, a_tm)]))
              | uu____14143 ->
                  let uu____14144 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name signature
                     in
                  FStar_Errors.raise_error uu____14144 r
               in
            let uu____14150 =
              let uu____14163 =
                let uu____14165 = FStar_Range.string_of_range r  in
                FStar_Util.format2 "implicit for wp of %s at %s"
                  eff_name.FStar_Ident.str uu____14165
                 in
              new_implicit_var uu____14163 r env wp_sort  in
            match uu____14150 with
            | (wp_uvar,uu____14173,g_wp_uvar) ->
                let eff_c =
                  let uu____14188 =
                    let uu____14189 =
                      let uu____14200 =
                        FStar_All.pipe_right wp_uvar
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____14200]  in
                    {
                      FStar_Syntax_Syntax.comp_univs = [u];
                      FStar_Syntax_Syntax.effect_name = eff_name;
                      FStar_Syntax_Syntax.result_typ = a_tm;
                      FStar_Syntax_Syntax.effect_args = uu____14189;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____14188  in
                let uu____14233 =
                  let uu____14234 =
                    let uu____14241 =
                      let uu____14242 =
                        let uu____14257 =
                          let uu____14266 =
                            FStar_Syntax_Syntax.null_binder
                              FStar_Syntax_Syntax.t_unit
                             in
                          [uu____14266]  in
                        (uu____14257, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____14242  in
                    FStar_Syntax_Syntax.mk uu____14241  in
                  uu____14234 FStar_Pervasives_Native.None r  in
                (uu____14233, g_wp_uvar)
  
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
                  let uu____14345 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____14345 r  in
                let uu____14355 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____14355 with
                | (uu____14364,signature) ->
                    let uu____14366 =
                      let uu____14367 = FStar_Syntax_Subst.compress signature
                         in
                      uu____14367.FStar_Syntax_Syntax.n  in
                    (match uu____14366 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14375) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____14423 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____14438 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____14440 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____14438 eff_name.FStar_Ident.str
                                       uu____14440) r
                                 in
                              (match uu____14423 with
                               | (is,g) ->
                                   let repr =
                                     let uu____14454 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____14454
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____14463 =
                                     let uu____14464 =
                                       let uu____14469 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____14469
                                        in
                                     uu____14464 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____14463, g))
                          | uu____14478 -> fail1 signature)
                     | uu____14479 -> fail1 signature)
  
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
            let uu____14510 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____14510
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
              let uu____14555 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____14555 with
              | (uu____14560,sig_tm) ->
                  let fail1 t =
                    let uu____14568 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____14568 r  in
                  let uu____14574 =
                    let uu____14575 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____14575.FStar_Syntax_Syntax.n  in
                  (match uu____14574 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____14579) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____14602)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____14624 -> fail1 sig_tm)
                   | uu____14625 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.lift_comp_t)
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____14646 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____14646
           then
             let uu____14651 = FStar_Syntax_Print.comp_to_string c  in
             let uu____14653 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____14651 uu____14653
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____14683 =
               let uu____14684 =
                 let uu____14690 =
                   let uu____14692 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____14694 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____14692 uu____14694
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____14690)  in
               FStar_Errors.raise_error uu____14684 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____14706,uu____14707::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____14775 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____14780,c1) ->
                    let uu____14802 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____14802
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____14837 -> err ())
              in
           let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____14839 =
             let uu____14850 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____14851 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____14850, (ct.FStar_Syntax_Syntax.result_typ), uu____14851)
              in
           match uu____14839 with
           | (u,a,c_is) ->
               let uu____14899 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____14899 with
                | (uu____14908,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____14919 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____14921 = FStar_Ident.string_of_lid tgt  in
                      let uu____14923 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____14919 uu____14921 s uu____14923
                       in
                    let uu____14926 =
                      let uu____14959 =
                        let uu____14960 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____14960.FStar_Syntax_Syntax.n  in
                      match uu____14959 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____15024 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____15024 with
                           | (a_b::bs1,c2) ->
                               let uu____15084 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____15146 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____15084, uu____15146))
                      | uu____15173 ->
                          let uu____15174 =
                            let uu____15180 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____15180)
                             in
                          FStar_Errors.raise_error uu____15174 r
                       in
                    (match uu____14926 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____15298 =
                           let uu____15305 =
                             let uu____15306 =
                               let uu____15307 =
                                 let uu____15314 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____15314, a)  in
                               FStar_Syntax_Syntax.NT uu____15307  in
                             [uu____15306]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____15305
                             (fun b  ->
                                let uu____15331 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____15333 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____15335 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____15337 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____15331 uu____15333 uu____15335
                                  uu____15337) r
                            in
                         (match uu____15298 with
                          | (rest_bs_uvars,g) ->
                              let substs =
                                FStar_List.map2
                                  (fun b  ->
                                     fun t  ->
                                       let uu____15374 =
                                         let uu____15381 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____15381, t)  in
                                       FStar_Syntax_Syntax.NT uu____15374)
                                  (a_b :: rest_bs) (a :: rest_bs_uvars)
                                 in
                              let guard_f =
                                let f_sort =
                                  let uu____15400 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                      (FStar_Syntax_Subst.subst substs)
                                     in
                                  FStar_All.pipe_right uu____15400
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____15406 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  effect_args_from_repr f_sort uu____15406
                                   in
                                FStar_List.fold_left2
                                  (fun g1  ->
                                     fun i1  ->
                                       fun i2  ->
                                         let uu____15415 =
                                           FStar_TypeChecker_Rel.teq env i1
                                             i2
                                            in
                                         FStar_TypeChecker_Env.conj_guard g1
                                           uu____15415)
                                  FStar_TypeChecker_Env.trivial_guard c_is
                                  f_sort_is
                                 in
                              let is =
                                let uu____15419 =
                                  FStar_TypeChecker_Env.is_layered_effect env
                                    tgt
                                   in
                                effect_args_from_repr
                                  lift_ct.FStar_Syntax_Syntax.result_typ
                                  uu____15419
                                 in
                              let c1 =
                                let uu____15422 =
                                  let uu____15423 =
                                    let uu____15434 =
                                      FStar_All.pipe_right is
                                        (FStar_List.map
                                           (FStar_Syntax_Subst.subst substs))
                                       in
                                    FStar_All.pipe_right uu____15434
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.as_arg)
                                     in
                                  {
                                    FStar_Syntax_Syntax.comp_univs =
                                      (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                    FStar_Syntax_Syntax.effect_name = tgt;
                                    FStar_Syntax_Syntax.result_typ = a;
                                    FStar_Syntax_Syntax.effect_args =
                                      uu____15423;
                                    FStar_Syntax_Syntax.flags =
                                      (ct.FStar_Syntax_Syntax.flags)
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____15422  in
                              ((let uu____15454 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____15454
                                then
                                  let uu____15459 =
                                    FStar_Syntax_Print.comp_to_string c1  in
                                  FStar_Util.print1 "} Lifted comp: %s\n"
                                    uu____15459
                                else ());
                               (let uu____15464 =
                                  FStar_TypeChecker_Env.conj_guard g guard_f
                                   in
                                (c1, uu____15464)))))))
  