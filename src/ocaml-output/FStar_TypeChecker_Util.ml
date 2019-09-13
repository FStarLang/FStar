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
  
let (close_layered_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun tms  ->
        fun lc  ->
          let bs =
            FStar_All.pipe_right bvs
              (FStar_List.map FStar_Syntax_Syntax.mk_binder)
             in
          let substs =
            FStar_List.map2
              (fun bv  -> fun tm  -> FStar_Syntax_Syntax.NT (bv, tm)) bvs tms
             in
          FStar_All.pipe_right lc
            (FStar_TypeChecker_Common.apply_lcomp
               (FStar_Syntax_Subst.subst_comp substs)
               (fun g  ->
                  let uu____1888 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____1888
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
              ({ FStar_Syntax_Syntax.ppname = uu____1911;
                 FStar_Syntax_Syntax.index = uu____1912;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____1914;
                     FStar_Syntax_Syntax.vars = uu____1915;_};_},uu____1916)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_wp_comp env [x] c
          | uu____1924 -> c
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_1936  ->
            match uu___0_1936 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1939 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____1964 =
            let uu____1967 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____1967 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____1964
            (fun c  ->
               (let uu____2023 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2023) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2027 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2027)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2038 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2038 with
                | (head1,uu____2055) ->
                    let uu____2076 =
                      let uu____2077 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2077.FStar_Syntax_Syntax.n  in
                    (match uu____2076 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2082 =
                           let uu____2084 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2084
                            in
                         Prims.op_Negation uu____2082
                     | uu____2085 -> true)))
              &&
              (let uu____2088 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2088)
  
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
            let uu____2116 =
              let uu____2118 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2118  in
            if uu____2116
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2125 = FStar_Syntax_Util.is_unit t  in
               if uu____2125
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
                    let uu____2134 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2134
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2139 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2139 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2149 =
                             let uu____2150 =
                               let uu____2155 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2156 =
                                 let uu____2157 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2166 =
                                   let uu____2177 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2177]  in
                                 uu____2157 :: uu____2166  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2155
                                 uu____2156
                                in
                             uu____2150 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2149)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2211 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2211
           then
             let uu____2216 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2218 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2220 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2216 uu____2218 uu____2220
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
                (let uu____2278 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____2278
                 then
                   let uu____2283 =
                     let uu____2285 = FStar_Syntax_Syntax.mk_Comp ct1  in
                     FStar_Syntax_Print.comp_to_string uu____2285  in
                   let uu____2286 =
                     let uu____2288 = FStar_Syntax_Syntax.mk_Comp ct2  in
                     FStar_Syntax_Print.comp_to_string uu____2288  in
                   FStar_Util.print2 "Binding c1:%s and c2:%s {\n" uu____2283
                     uu____2286
                 else ());
                (let ed = FStar_TypeChecker_Env.get_effect_decl env m  in
                 let uu____2293 =
                   let uu____2304 =
                     FStar_List.hd ct1.FStar_Syntax_Syntax.comp_univs  in
                   let uu____2305 =
                     FStar_List.map FStar_Pervasives_Native.fst
                       ct1.FStar_Syntax_Syntax.effect_args
                      in
                   (uu____2304, (ct1.FStar_Syntax_Syntax.result_typ),
                     uu____2305)
                    in
                 match uu____2293 with
                 | (u1,t1,is1) ->
                     let uu____2339 =
                       let uu____2350 =
                         FStar_List.hd ct2.FStar_Syntax_Syntax.comp_univs  in
                       let uu____2351 =
                         FStar_List.map FStar_Pervasives_Native.fst
                           ct2.FStar_Syntax_Syntax.effect_args
                          in
                       (uu____2350, (ct2.FStar_Syntax_Syntax.result_typ),
                         uu____2351)
                        in
                     (match uu____2339 with
                      | (u2,t2,is2) ->
                          let uu____2385 =
                            FStar_TypeChecker_Env.inst_tscheme_with
                              ed.FStar_Syntax_Syntax.bind_wp [u1; u2]
                             in
                          (match uu____2385 with
                           | (uu____2394,bind_t) ->
                               let bind_t_shape_error s =
                                 let uu____2409 =
                                   let uu____2411 =
                                     FStar_Syntax_Print.term_to_string bind_t
                                      in
                                   FStar_Util.format2
                                     "bind %s does not have proper shape (reason:%s)"
                                     uu____2411 s
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____2409)
                                  in
                               let uu____2415 =
                                 let uu____2460 =
                                   let uu____2461 =
                                     FStar_Syntax_Subst.compress bind_t  in
                                   uu____2461.FStar_Syntax_Syntax.n  in
                                 match uu____2460 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____2537 =
                                       FStar_Syntax_Subst.open_comp bs c  in
                                     (match uu____2537 with
                                      | (a_b::b_b::bs1,c1) ->
                                          let uu____2622 =
                                            let uu____2649 =
                                              FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   (Prims.of_int (2))) bs1
                                               in
                                            FStar_All.pipe_right uu____2649
                                              (fun uu____2734  ->
                                                 match uu____2734 with
                                                 | (l1,l2) ->
                                                     let uu____2815 =
                                                       FStar_List.hd l2  in
                                                     let uu____2828 =
                                                       let uu____2835 =
                                                         FStar_List.tl l2  in
                                                       FStar_List.hd
                                                         uu____2835
                                                        in
                                                     (l1, uu____2815,
                                                       uu____2828))
                                             in
                                          (match uu____2622 with
                                           | (rest_bs,f_b,g_b) ->
                                               let uu____2963 =
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                   c1
                                                  in
                                               (a_b, b_b, rest_bs, f_b, g_b,
                                                 uu____2963)))
                                 | uu____2996 ->
                                     let uu____2997 =
                                       bind_t_shape_error
                                         "Either not an arrow or not enough binders"
                                        in
                                     FStar_Errors.raise_error uu____2997 r1
                                  in
                               (match uu____2415 with
                                | (a_b,b_b,rest_bs,f_b,g_b,bind_ct) ->
                                    let uu____3122 =
                                      let uu____3129 =
                                        let uu____3130 =
                                          let uu____3131 =
                                            let uu____3138 =
                                              FStar_All.pipe_right a_b
                                                FStar_Pervasives_Native.fst
                                               in
                                            (uu____3138, t1)  in
                                          FStar_Syntax_Syntax.NT uu____3131
                                           in
                                        let uu____3149 =
                                          let uu____3152 =
                                            let uu____3153 =
                                              let uu____3160 =
                                                FStar_All.pipe_right b_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____3160, t2)  in
                                            FStar_Syntax_Syntax.NT uu____3153
                                             in
                                          [uu____3152]  in
                                        uu____3130 :: uu____3149  in
                                      FStar_TypeChecker_Env.uvars_for_binders
                                        env rest_bs uu____3129
                                        (fun b1  ->
                                           let uu____3175 =
                                             FStar_Syntax_Print.binder_to_string
                                               b1
                                              in
                                           let uu____3177 =
                                             FStar_Range.string_of_range r1
                                              in
                                           FStar_Util.format3
                                             "implicit var for binder %s of %s:bind at %s"
                                             uu____3175
                                             (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             uu____3177) r1
                                       in
                                    (match uu____3122 with
                                     | (rest_bs_uvars,g_uvars) ->
                                         let subst1 =
                                           FStar_List.map2
                                             (fun b1  ->
                                                fun t  ->
                                                  let uu____3214 =
                                                    let uu____3221 =
                                                      FStar_All.pipe_right b1
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    (uu____3221, t)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3214) (a_b :: b_b
                                             :: rest_bs) (t1 :: t2 ::
                                             rest_bs_uvars)
                                            in
                                         let f_guard =
                                           let f_sort_is =
                                             let uu____3248 =
                                               let uu____3249 =
                                                 let uu____3252 =
                                                   let uu____3253 =
                                                     FStar_All.pipe_right f_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3253.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3252
                                                  in
                                               uu____3249.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3248 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____3264,uu____3265::is)
                                                 ->
                                                 let uu____3307 =
                                                   FStar_All.pipe_right is
                                                     (FStar_List.map
                                                        FStar_Pervasives_Native.fst)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3307
                                                   (FStar_List.map
                                                      (FStar_Syntax_Subst.subst
                                                         subst1))
                                             | uu____3340 ->
                                                 let uu____3341 =
                                                   bind_t_shape_error
                                                     "f's type is not a repr type"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3341 r1
                                              in
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun i1  ->
                                                  fun f_i1  ->
                                                    let uu____3357 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env i1 f_i1
                                                       in
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g uu____3357)
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
                                             let uu____3376 =
                                               let uu____3377 =
                                                 let uu____3380 =
                                                   let uu____3381 =
                                                     FStar_All.pipe_right g_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3381.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3380
                                                  in
                                               uu____3377.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3376 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs,c) ->
                                                 let uu____3414 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c
                                                    in
                                                 (match uu____3414 with
                                                  | (bs1,c1) ->
                                                      let bs_subst =
                                                        let uu____3424 =
                                                          let uu____3431 =
                                                            let uu____3432 =
                                                              FStar_List.hd
                                                                bs1
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3432
                                                              FStar_Pervasives_Native.fst
                                                             in
                                                          let uu____3453 =
                                                            let uu____3456 =
                                                              FStar_All.pipe_right
                                                                x_a
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3456
                                                              FStar_Syntax_Syntax.bv_to_name
                                                             in
                                                          (uu____3431,
                                                            uu____3453)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____3424
                                                         in
                                                      let c2 =
                                                        FStar_Syntax_Subst.subst_comp
                                                          [bs_subst] c1
                                                         in
                                                      let uu____3470 =
                                                        let uu____3471 =
                                                          FStar_Syntax_Subst.compress
                                                            (FStar_Syntax_Util.comp_result
                                                               c2)
                                                           in
                                                        uu____3471.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____3470 with
                                                       | FStar_Syntax_Syntax.Tm_app
                                                           (uu____3476,uu____3477::is)
                                                           ->
                                                           let uu____3519 =
                                                             FStar_All.pipe_right
                                                               is
                                                               (FStar_List.map
                                                                  FStar_Pervasives_Native.fst)
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____3519
                                                             (FStar_List.map
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1))
                                                       | uu____3552 ->
                                                           let uu____3553 =
                                                             bind_t_shape_error
                                                               "g's type is not a repr type"
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____3553 r1))
                                             | uu____3562 ->
                                                 let uu____3563 =
                                                   bind_t_shape_error
                                                     "g's type is not an arrow"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3563 r1
                                              in
                                           let env_g =
                                             FStar_TypeChecker_Env.push_binders
                                               env [x_a]
                                              in
                                           let uu____3585 =
                                             FStar_List.fold_left2
                                               (fun g  ->
                                                  fun i1  ->
                                                    fun g_i1  ->
                                                      let uu____3593 =
                                                        FStar_TypeChecker_Rel.teq
                                                          env_g i1 g_i1
                                                         in
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g uu____3593)
                                               FStar_TypeChecker_Env.trivial_guard
                                               is2 g_sort_is
                                              in
                                           FStar_All.pipe_right uu____3585
                                             (FStar_TypeChecker_Env.close_guard
                                                env [x_a])
                                            in
                                         let is =
                                           let uu____3609 =
                                             let uu____3610 =
                                               FStar_Syntax_Subst.compress
                                                 bind_ct.FStar_Syntax_Syntax.result_typ
                                                in
                                             uu____3610.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3609 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____3615,uu____3616::is) ->
                                               let uu____3658 =
                                                 FStar_All.pipe_right is
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3658
                                                 (FStar_List.map
                                                    (FStar_Syntax_Subst.subst
                                                       subst1))
                                           | uu____3691 ->
                                               let uu____3692 =
                                                 bind_t_shape_error
                                                   "return type is not a repr type"
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____3692 r1
                                            in
                                         let c =
                                           let uu____3702 =
                                             let uu____3703 =
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
                                                 = uu____3703;
                                               FStar_Syntax_Syntax.flags =
                                                 flags
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____3702
                                            in
                                         ((let uu____3723 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffects")
                                              in
                                           if uu____3723
                                           then
                                             let uu____3728 =
                                               FStar_Syntax_Print.comp_to_string
                                                 c
                                                in
                                             FStar_Util.print1
                                               "} c after bind: %s\n"
                                               uu____3728
                                           else ());
                                          (let uu____3733 =
                                             FStar_TypeChecker_Env.conj_guards
                                               [g_uvars; f_guard; g_guard]
                                              in
                                           (c, uu____3733))))))))
  
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
                let uu____3778 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____3804 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____3804 with
                  | (a,kwp) ->
                      let uu____3835 = destruct_wp_comp ct1  in
                      let uu____3842 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____3835, uu____3842)
                   in
                match uu____3778 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____3895 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____3895]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____3915 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3915]
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
                      let uu____3962 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____3971 =
                        let uu____3982 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____3991 =
                          let uu____4002 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____4011 =
                            let uu____4022 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____4031 =
                              let uu____4042 =
                                let uu____4051 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____4051  in
                              [uu____4042]  in
                            uu____4022 :: uu____4031  in
                          uu____4002 :: uu____4011  in
                        uu____3982 :: uu____3991  in
                      uu____3962 :: uu____3971  in
                    let wp =
                      let uu____4103 =
                        let uu____4108 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md
                            md.FStar_Syntax_Syntax.bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4108 wp_args  in
                      uu____4103 FStar_Pervasives_Native.None
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
              let uu____4156 = lift_comps env c1 c2 b true  in
              match uu____4156 with
              | (m,c11,c21,g_lift) ->
                  let uu____4174 =
                    let uu____4179 = FStar_Syntax_Util.comp_to_comp_typ c11
                       in
                    let uu____4180 = FStar_Syntax_Util.comp_to_comp_typ c21
                       in
                    (uu____4179, uu____4180)  in
                  (match uu____4174 with
                   | (ct1,ct2) ->
                       let uu____4187 =
                         let uu____4192 =
                           FStar_TypeChecker_Env.is_layered_effect env m  in
                         if uu____4192
                         then mk_layered_bind env m ct1 b ct2 flags r1
                         else
                           (let uu____4201 =
                              mk_non_layered_bind env m ct1 b ct2 flags r1
                               in
                            (uu____4201, FStar_TypeChecker_Env.trivial_guard))
                          in
                       (match uu____4187 with
                        | (c,g_bind) ->
                            let uu____4208 =
                              FStar_TypeChecker_Env.conj_guard g_lift g_bind
                               in
                            (c, uu____4208)))
  
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
          let c_eff_name =
            let uu____4244 =
              FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
            FStar_All.pipe_right uu____4244
              (FStar_TypeChecker_Env.norm_eff_name env)
             in
          let edge =
            let uu____4248 =
              FStar_TypeChecker_Env.monad_leq env
                FStar_Parser_Const.effect_PURE_lid c_eff_name
               in
            match uu____4248 with
            | FStar_Pervasives_Native.Some edge -> edge
            | FStar_Pervasives_Native.None  ->
                failwith
                  (Prims.op_Hat
                     "Impossible! lift_wp_and_bind_with: did not find a lift from PURE to "
                     c_eff_name.FStar_Ident.str)
             in
          let pure_c =
            let uu____4254 =
              let uu____4255 =
                let uu____4266 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____4266]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4255;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4254  in
          let uu____4299 =
            (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
              env pure_c
             in
          match uu____4299 with
          | (m_c,g_lift) ->
              let uu____4310 =
                mk_bind env pure_c FStar_Pervasives_Native.None c flags r  in
              (match uu____4310 with
               | (bind_c,g_bind) ->
                   let uu____4321 =
                     FStar_TypeChecker_Env.conj_guard g_lift g_bind  in
                   (bind_c, uu____4321))
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____4334 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4340  ->
              match uu___1_4340 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4343 -> false))
       in
    if uu____4334
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4355  ->
              match uu___2_4355 with
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
        let uu____4383 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4383
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____4394 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____4394  in
           let pure_assume_wp1 =
             let uu____4399 = FStar_TypeChecker_Env.get_range env  in
             let uu____4400 =
               let uu____4405 =
                 let uu____4406 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____4406]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4405  in
             uu____4400 FStar_Pervasives_Native.None uu____4399  in
           let uu____4439 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           lift_wp_and_bind_with env pure_assume_wp1 c uu____4439)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4467 =
          let uu____4468 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____4468 with
          | (c,g_c) ->
              let uu____4479 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4479
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____4493 = weaken_comp env c f1  in
                     (match uu____4493 with
                      | (c1,g_w) ->
                          let uu____4504 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____4504)))
           in
        let uu____4505 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____4505 weaken
  
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
                 let uu____4562 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____4562  in
               let pure_assert_wp1 =
                 let uu____4567 =
                   let uu____4572 =
                     let uu____4573 =
                       let uu____4582 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____4582
                        in
                     [uu____4573]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____4572
                    in
                 uu____4567 FStar_Pervasives_Native.None r  in
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
            let uu____4652 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____4652
            then (lc, g0)
            else
              (let flags =
                 let uu____4664 =
                   let uu____4672 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____4672
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4664 with
                 | (maybe_trivial_post,flags) ->
                     let uu____4702 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_4710  ->
                               match uu___3_4710 with
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
                               | uu____4713 -> []))
                        in
                     FStar_List.append flags uu____4702
                  in
               let strengthen uu____4723 =
                 let uu____4724 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____4724 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____4743 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____4743 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____4750 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4750
                              then
                                let uu____4754 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____4756 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____4754 uu____4756
                              else ());
                             (let uu____4761 =
                                strengthen_comp env reason c f flags  in
                              match uu____4761 with
                              | (c1,g_s) ->
                                  let uu____4772 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____4772))))
                  in
               let uu____4773 =
                 let uu____4774 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____4774
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____4773,
                 (let uu___588_4776 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___588_4776.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___588_4776.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___588_4776.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_4785  ->
            match uu___4_4785 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4789 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____4818 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4818
          then e
          else
            (let uu____4825 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4828 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4828)
                in
             if uu____4825
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
          fun uu____4881  ->
            match uu____4881 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4901 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____4901 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____4914 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____4914
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____4924 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____4924
                       then
                         let uu____4929 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____4929
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____4936 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____4936
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____4945 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____4945
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____4952 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____4952
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____4968 =
                  let uu____4969 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____4969
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____4977 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____4977, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____4980 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____4980 with
                     | (c1,g_c1) ->
                         let uu____4991 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____4991 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____5011  ->
                                    let uu____5012 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____5014 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____5019 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____5012 uu____5014 uu____5019);
                               (let aux uu____5037 =
                                  let uu____5038 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____5038
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5069
                                        ->
                                        let uu____5070 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5070
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5102 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5102
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____5147 =
                                  let uu____5148 =
                                    let uu____5150 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____5150  in
                                  if uu____5148
                                  then
                                    let uu____5164 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____5164
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5187 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5187))
                                  else
                                    (let uu____5202 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____5202
                                     then
                                       let close1 x reason c =
                                         let uu____5243 =
                                           let uu____5245 =
                                             let uu____5246 =
                                               FStar_All.pipe_right c
                                                 FStar_Syntax_Util.comp_effect_name
                                                in
                                             FStar_All.pipe_right uu____5246
                                               (FStar_TypeChecker_Env.norm_eff_name
                                                  env)
                                              in
                                           FStar_All.pipe_right uu____5245
                                             (FStar_TypeChecker_Env.is_layered_effect
                                                env)
                                            in
                                         if uu____5243
                                         then FStar_Util.Inl (c, reason)
                                         else
                                           (let x1 =
                                              let uu___659_5271 = x  in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___659_5271.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___659_5271.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (FStar_Syntax_Util.comp_result
                                                     c1)
                                              }  in
                                            let uu____5272 =
                                              let uu____5278 =
                                                close_wp_comp_if_refinement_t
                                                  env
                                                  x1.FStar_Syntax_Syntax.sort
                                                  x1 c
                                                 in
                                              (uu____5278, reason)  in
                                            FStar_Util.Inl uu____5272)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____5314 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____5314
                                             (close1 x "c1 Tot")
                                       | (uu____5328,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____5351,uu____5352) -> aux ()
                                     else
                                       (let uu____5367 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____5367
                                        then
                                          let uu____5380 =
                                            let uu____5386 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____5386, "both GTot")  in
                                          FStar_Util.Inl uu____5380
                                        else aux ()))
                                   in
                                let uu____5397 = try_simplify ()  in
                                match uu____5397 with
                                | FStar_Util.Inl (c,reason) ->
                                    (debug1
                                       (fun uu____5427  ->
                                          let uu____5428 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____5428);
                                     (let uu____5431 =
                                        FStar_TypeChecker_Env.conj_guard g_c1
                                          g_c2
                                         in
                                      (c, uu____5431)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____5443  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____5469 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____5469 with
                                        | (c,g_bind) ->
                                            let uu____5480 =
                                              let uu____5481 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5481 g_bind
                                               in
                                            (c, uu____5480)
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
                                        let uu____5508 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5508 with
                                        | (m,uu____5520,lift2) ->
                                            let uu____5522 =
                                              lift_comp env c22 lift2  in
                                            (match uu____5522 with
                                             | (c23,g2) ->
                                                 let uu____5533 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____5533 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let vc1 =
                                                        let uu____5551 =
                                                          let uu____5556 =
                                                            let uu____5557 =
                                                              FStar_All.pipe_right
                                                                md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                                FStar_Util.must
                                                               in
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              uu____5557
                                                             in
                                                          let uu____5560 =
                                                            let uu____5561 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5570 =
                                                              let uu____5581
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5581]
                                                               in
                                                            uu____5561 ::
                                                              uu____5570
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5556
                                                            uu____5560
                                                           in
                                                        uu____5551
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5614 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____5614 with
                                                       | (c,g_s) ->
                                                           let uu____5629 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____5629))))
                                         in
                                      let uu____5630 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5646 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____5646, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____5630 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____5662 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____5662
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____5671 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____5671
                                             then
                                               (debug1
                                                  (fun uu____5685  ->
                                                     let uu____5686 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____5688 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____5686 uu____5688);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____5696 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____5699 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____5699)
                                                   in
                                                if uu____5696
                                                then
                                                  let e1' =
                                                    let uu____5724 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____5724
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____5736  ->
                                                        let uu____5737 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____5739 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____5737
                                                          uu____5739);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____5754  ->
                                                        let uu____5755 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5757 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____5755
                                                          uu____5757);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____5764 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____5764
                                                       in
                                                    let uu____5765 =
                                                      let uu____5770 =
                                                        let uu____5771 =
                                                          let uu____5772 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____5772]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____5771
                                                         in
                                                      weaken_comp uu____5770
                                                        c21 x_eq_e
                                                       in
                                                    match uu____5765 with
                                                    | (c22,g_w) ->
                                                        let uu____5797 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____5797
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____5808 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____5808))))))
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
                     let uu___773_5908 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___773_5908.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___773_5908.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___773_5908.FStar_Syntax_Syntax.effect_args);
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
  
let mk_layered_conjunction :
  'Auu____6032 .
    'Auu____6032 ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.comp_typ ->
                FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp
  =
  fun _env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                let uu____6068 =
                  let uu____6073 =
                    let uu____6074 =
                      FStar_All.pipe_right ed.FStar_Syntax_Syntax.match_wps
                        FStar_Util.right
                       in
                    uu____6074.FStar_Syntax_Syntax.conjunction  in
                  FStar_TypeChecker_Env.inst_tscheme_with uu____6073 [u_a]
                   in
                match uu____6068 with
                | (uu____6079,conjunction) ->
                    let uu____6081 =
                      let uu____6094 =
                        FStar_List.map FStar_Pervasives_Native.fst
                          ct1.FStar_Syntax_Syntax.effect_args
                         in
                      let uu____6113 =
                        FStar_List.map FStar_Pervasives_Native.fst
                          ct2.FStar_Syntax_Syntax.effect_args
                         in
                      (uu____6094, uu____6113)  in
                    (match uu____6081 with
                     | (is1,is2) ->
                         let uu____6158 =
                           let uu____6197 =
                             let uu____6198 =
                               FStar_Syntax_Subst.compress conjunction  in
                             uu____6198.FStar_Syntax_Syntax.n  in
                           match uu____6197 with
                           | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6241)
                               ->
                               let uu____6266 =
                                 FStar_Syntax_Subst.open_term bs body  in
                               (match uu____6266 with
                                | (bs1,body1) ->
                                    let uu____6311 =
                                      let uu____6330 = FStar_List.hd bs1  in
                                      let uu____6343 = FStar_List.tl bs1  in
                                      (uu____6330, uu____6343)  in
                                    (match uu____6311 with
                                     | (a_b,bs2) ->
                                         let uu____6440 =
                                           FStar_List.splitAt
                                             (FStar_List.length is1) bs2
                                            in
                                         (match uu____6440 with
                                          | (f_bs,bs3) ->
                                              let uu____6541 =
                                                FStar_List.splitAt
                                                  (FStar_List.length is1) bs3
                                                 in
                                              (match uu____6541 with
                                               | (g_bs,bs4) ->
                                                   let uu____6642 =
                                                     FStar_List.hd bs4  in
                                                   let uu____6655 =
                                                     FStar_Syntax_Util.unascribe
                                                       body1
                                                      in
                                                   (a_b, f_bs, g_bs,
                                                     uu____6642, uu____6655)))))
                           | uu____6684 -> failwith "Impossible"  in
                         (match uu____6158 with
                          | (a_b,f_bs,g_bs,p_b,body) ->
                              let substs =
                                let uu____6788 =
                                  let uu____6791 =
                                    let uu____6792 =
                                      let uu____6799 =
                                        FStar_All.pipe_right a_b
                                          FStar_Pervasives_Native.fst
                                         in
                                      (uu____6799, a)  in
                                    FStar_Syntax_Syntax.NT uu____6792  in
                                  [uu____6791]  in
                                let uu____6810 =
                                  let uu____6813 =
                                    FStar_List.map2
                                      (fun f_b  ->
                                         fun i  ->
                                           let uu____6837 =
                                             let uu____6844 =
                                               FStar_All.pipe_right f_b
                                                 FStar_Pervasives_Native.fst
                                                in
                                             (uu____6844, i)  in
                                           FStar_Syntax_Syntax.NT uu____6837)
                                      f_bs is1
                                     in
                                  let uu____6855 =
                                    let uu____6858 =
                                      FStar_List.map2
                                        (fun g_b  ->
                                           fun i  ->
                                             let uu____6882 =
                                               let uu____6889 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               (uu____6889, i)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____6882) g_bs is2
                                       in
                                    let uu____6900 =
                                      let uu____6903 =
                                        let uu____6904 =
                                          let uu____6911 =
                                            FStar_All.pipe_right p_b
                                              FStar_Pervasives_Native.fst
                                             in
                                          (uu____6911, p)  in
                                        FStar_Syntax_Syntax.NT uu____6904  in
                                      [uu____6903]  in
                                    FStar_List.append uu____6858 uu____6900
                                     in
                                  FStar_List.append uu____6813 uu____6855  in
                                FStar_List.append uu____6788 uu____6810  in
                              let body1 =
                                FStar_Syntax_Subst.subst substs body  in
                              let is =
                                let uu____6926 =
                                  let uu____6927 =
                                    FStar_Syntax_Subst.compress body1  in
                                  uu____6927.FStar_Syntax_Syntax.n  in
                                match uu____6926 with
                                | FStar_Syntax_Syntax.Tm_app
                                    (uu____6932,a1::args) ->
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst args
                                | uu____6987 -> failwith "Impossible"  in
                              let uu____6991 =
                                let uu____6992 =
                                  FStar_All.pipe_right is
                                    (FStar_List.map
                                       FStar_Syntax_Syntax.as_arg)
                                   in
                                {
                                  FStar_Syntax_Syntax.comp_univs = [u_a];
                                  FStar_Syntax_Syntax.effect_name =
                                    (ed.FStar_Syntax_Syntax.mname);
                                  FStar_Syntax_Syntax.result_typ = a;
                                  FStar_Syntax_Syntax.effect_args =
                                    uu____6992;
                                  FStar_Syntax_Syntax.flags = []
                                }  in
                              FStar_Syntax_Syntax.mk_Comp uu____6991))
  
let (mk_non_layered_conjunction :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                let uu____7051 =
                  FStar_Syntax_Util.get_match_with_close_wps
                    ed.FStar_Syntax_Syntax.match_wps
                   in
                match uu____7051 with
                | (if_then_else1,uu____7059,uu____7060) ->
                    let uu____7061 = destruct_wp_comp ct1  in
                    (match uu____7061 with
                     | (uu____7068,uu____7069,wp_t) ->
                         let uu____7071 = destruct_wp_comp ct2  in
                         (match uu____7071 with
                          | (uu____7078,uu____7079,wp_e) ->
                              let wp =
                                let uu____7084 =
                                  FStar_Range.union_ranges
                                    wp_t.FStar_Syntax_Syntax.pos
                                    wp_e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____7085 =
                                  let uu____7090 =
                                    FStar_TypeChecker_Env.inst_effect_fun_with
                                      [u_a] env ed if_then_else1
                                     in
                                  let uu____7091 =
                                    let uu____7092 =
                                      FStar_Syntax_Syntax.as_arg a  in
                                    let uu____7101 =
                                      let uu____7112 =
                                        FStar_Syntax_Syntax.as_arg p  in
                                      let uu____7121 =
                                        let uu____7132 =
                                          FStar_Syntax_Syntax.as_arg wp_t  in
                                        let uu____7141 =
                                          let uu____7152 =
                                            FStar_Syntax_Syntax.as_arg wp_e
                                             in
                                          [uu____7152]  in
                                        uu____7132 :: uu____7141  in
                                      uu____7112 :: uu____7121  in
                                    uu____7092 :: uu____7101  in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____7090
                                    uu____7091
                                   in
                                uu____7085 FStar_Pervasives_Native.None
                                  uu____7084
                                 in
                              mk_comp ed u_a a wp []))
  
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
               fun uu____7270  ->
                 match uu____7270 with
                 | (uu____7284,eff_label,uu____7286,uu____7287) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____7300 =
          let uu____7308 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____7346  ->
                    match uu____7346 with
                    | (uu____7361,uu____7362,flags,uu____7364) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_7381  ->
                                match uu___5_7381 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____7384 -> false))))
             in
          if uu____7308
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____7300 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____7421 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____7423 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____7423
              then
                let uu____7430 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____7430, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____7437 =
                       let uu____7446 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7446]  in
                     let uu____7465 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7437 uu____7465  in
                   let kwp =
                     let uu____7471 =
                       let uu____7480 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7480]  in
                     let uu____7499 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7471 uu____7499  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7506 =
                       let uu____7507 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7507]  in
                     let uu____7526 =
                       let uu____7529 =
                         let uu____7536 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7536
                          in
                       let uu____7537 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7529 uu____7537  in
                     FStar_Syntax_Util.abs uu____7506 uu____7526
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
                   let uu____7561 =
                     should_not_inline_whole_match ||
                       (let uu____7564 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7564)
                      in
                   if uu____7561 then cthen true else cthen false  in
                 let uu____7571 =
                   FStar_List.fold_right
                     (fun uu____7622  ->
                        fun uu____7623  ->
                          match (uu____7622, uu____7623) with
                          | ((g,eff_label,uu____7677,cthen),(uu____7679,celse,g_comp))
                              ->
                              let uu____7720 =
                                let uu____7725 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____7725
                                 in
                              (match uu____7720 with
                               | (cthen1,gthen) ->
                                   let uu____7736 =
                                     let uu____7745 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____7745 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____7768 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____7769 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____7768, uu____7769, g_lift)
                                      in
                                   (match uu____7736 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          if
                                            md.FStar_Syntax_Syntax.is_layered
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____7835 =
                                          fn env md u_res_t res_t g ct_then
                                            ct_else
                                           in
                                        let uu____7836 =
                                          let uu____7837 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_comp gthen
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____7837 g_lift
                                           in
                                        ((FStar_Pervasives_Native.Some md),
                                          uu____7835, uu____7836)))) lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____7571 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____7871::[] -> (comp, g_comp)
                      | uu____7914 ->
                          let uu____7931 =
                            let uu____7933 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            uu____7933.FStar_Syntax_Syntax.is_layered  in
                          if uu____7931
                          then (comp, g_comp)
                          else
                            (let comp1 =
                               FStar_TypeChecker_Env.comp_to_comp_typ env
                                 comp
                                in
                             let md1 =
                               FStar_TypeChecker_Env.get_effect_decl env
                                 comp1.FStar_Syntax_Syntax.effect_name
                                in
                             let uu____7945 = destruct_wp_comp comp1  in
                             match uu____7945 with
                             | (uu____7956,uu____7957,wp) ->
                                 let uu____7959 =
                                   FStar_Syntax_Util.get_match_with_close_wps
                                     md1.FStar_Syntax_Syntax.match_wps
                                    in
                                 (match uu____7959 with
                                  | (uu____7970,ite_wp,uu____7972) ->
                                      let wp1 =
                                        let uu____7976 =
                                          let uu____7981 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [u_res_t] env md1 ite_wp
                                             in
                                          let uu____7982 =
                                            let uu____7983 =
                                              FStar_Syntax_Syntax.as_arg
                                                res_t
                                               in
                                            let uu____7992 =
                                              let uu____8003 =
                                                FStar_Syntax_Syntax.as_arg wp
                                                 in
                                              [uu____8003]  in
                                            uu____7983 :: uu____7992  in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            uu____7981 uu____7982
                                           in
                                        uu____7976
                                          FStar_Pervasives_Native.None
                                          wp.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____8036 =
                                        mk_comp md1 u_res_t res_t wp1
                                          bind_cases_flags
                                         in
                                      (uu____8036, g_comp)))))
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
          let uu____8070 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____8070 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____8086 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____8092 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____8086 uu____8092
              else
                (let uu____8101 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____8107 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____8101 uu____8107)
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
          let uu____8132 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____8132
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____8135 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____8135
        then u_res
        else
          (let is_total =
             let uu____8142 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____8142
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____8153 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____8153 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8156 =
                    let uu____8162 =
                      let uu____8164 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____8164
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____8162)
                     in
                  FStar_Errors.raise_error uu____8156
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
      let uu____8188 = destruct_wp_comp ct  in
      match uu____8188 with
      | (u_t,t,wp) ->
          let vc =
            let uu____8207 = FStar_TypeChecker_Env.get_range env  in
            let uu____8208 =
              let uu____8213 =
                let uu____8214 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____8214
                 in
              let uu____8217 =
                let uu____8218 = FStar_Syntax_Syntax.as_arg t  in
                let uu____8227 =
                  let uu____8238 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____8238]  in
                uu____8218 :: uu____8227  in
              FStar_Syntax_Syntax.mk_Tm_app uu____8213 uu____8217  in
            uu____8208 FStar_Pervasives_Native.None uu____8207  in
          let uu____8271 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____8271)
  
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
               let uu____8312 =
                 let uu____8313 = FStar_Syntax_Subst.compress t2  in
                 uu____8313.FStar_Syntax_Syntax.n  in
               match uu____8312 with
               | FStar_Syntax_Syntax.Tm_type uu____8317 -> true
               | uu____8319 -> false  in
             let uu____8321 =
               let uu____8322 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____8322.FStar_Syntax_Syntax.n  in
             match uu____8321 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____8330 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____8340 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____8340
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____8343 =
                     let uu____8344 =
                       let uu____8345 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____8345
                        in
                     (FStar_Pervasives_Native.None, uu____8344)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____8343
                    in
                 let e1 =
                   let uu____8351 =
                     let uu____8356 =
                       let uu____8357 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____8357]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____8356  in
                   uu____8351 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____8382 -> (e, lc))
  
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
          (let uu____8417 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____8417
           then
             let uu____8420 = FStar_Syntax_Print.term_to_string e  in
             let uu____8422 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____8424 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____8420 uu____8422 uu____8424
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____8434 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____8434 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____8459 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____8485 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____8485, false)
             else
               (let uu____8495 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____8495, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____8508) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____8520 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____8520
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1020_8536 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1020_8536.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1020_8536.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1020_8536.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____8543 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____8543 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____8559 =
                      let uu____8560 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____8560 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____8580 =
                            let uu____8582 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____8582 = FStar_Syntax_Util.Equal  in
                          if uu____8580
                          then
                            ((let uu____8589 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____8589
                              then
                                let uu____8593 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____8595 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____8593 uu____8595
                              else ());
                             (let uu____8600 = set_result_typ1 c  in
                              (uu____8600, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____8607 ->
                                   true
                               | uu____8615 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____8624 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____8624
                                  in
                               let lc1 =
                                 let uu____8626 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____8627 =
                                   let uu____8628 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____8628)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____8626 uu____8627
                                  in
                               ((let uu____8632 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____8632
                                 then
                                   let uu____8636 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____8638 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____8640 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____8642 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____8636 uu____8638 uu____8640
                                     uu____8642
                                 else ());
                                (let uu____8647 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____8647 with
                                 | (c1,g_lc) ->
                                     let uu____8658 = set_result_typ1 c1  in
                                     let uu____8659 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____8658, uu____8659)))
                             else
                               ((let uu____8663 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____8663
                                 then
                                   let uu____8667 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____8669 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____8667 uu____8669
                                 else ());
                                (let uu____8674 = set_result_typ1 c  in
                                 (uu____8674, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1057_8678 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1057_8678.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1057_8678.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1057_8678.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____8688 =
                      let uu____8689 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____8689
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____8699 =
                           let uu____8700 = FStar_Syntax_Subst.compress f1
                              in
                           uu____8700.FStar_Syntax_Syntax.n  in
                         match uu____8699 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____8707,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____8709;
                                           FStar_Syntax_Syntax.vars =
                                             uu____8710;_},uu____8711)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1073_8737 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1073_8737.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1073_8737.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1073_8737.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____8738 ->
                             let uu____8739 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____8739 with
                              | (c,g_c) ->
                                  ((let uu____8751 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____8751
                                    then
                                      let uu____8755 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____8757 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____8759 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____8761 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____8755 uu____8757 uu____8759
                                        uu____8761
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
                                        let uu____8774 =
                                          let uu____8779 =
                                            let uu____8780 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____8780]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____8779
                                           in
                                        uu____8774
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____8807 =
                                      let uu____8812 =
                                        FStar_All.pipe_left
                                          (fun _8833  ->
                                             FStar_Pervasives_Native.Some
                                               _8833)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____8834 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____8835 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____8836 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____8812
                                        uu____8834 e uu____8835 uu____8836
                                       in
                                    match uu____8807 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1091_8844 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1091_8844.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1091_8844.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____8846 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____8846
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____8849 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____8849 with
                                         | (c2,g_lc) ->
                                             ((let uu____8861 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____8861
                                               then
                                                 let uu____8865 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____8865
                                               else ());
                                              (let uu____8870 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____8870))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_8879  ->
                              match uu___6_8879 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____8882 -> []))
                       in
                    let lc1 =
                      let uu____8884 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____8884 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1107_8886 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1107_8886.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1107_8886.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1107_8886.FStar_TypeChecker_Common.implicits)
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
        let uu____8922 =
          let uu____8925 =
            let uu____8930 =
              let uu____8931 =
                let uu____8940 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____8940  in
              [uu____8931]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____8930  in
          uu____8925 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____8922  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____8963 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____8963
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____8982 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____8998 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____9015 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____9015
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____9031)::(ens,uu____9033)::uu____9034 ->
                    let uu____9077 =
                      let uu____9080 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____9080  in
                    let uu____9081 =
                      let uu____9082 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____9082  in
                    (uu____9077, uu____9081)
                | uu____9085 ->
                    let uu____9096 =
                      let uu____9102 =
                        let uu____9104 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____9104
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____9102)
                       in
                    FStar_Errors.raise_error uu____9096
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____9124)::uu____9125 ->
                    let uu____9152 =
                      let uu____9157 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____9157
                       in
                    (match uu____9152 with
                     | (us_r,uu____9189) ->
                         let uu____9190 =
                           let uu____9195 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____9195
                            in
                         (match uu____9190 with
                          | (us_e,uu____9227) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____9230 =
                                  let uu____9231 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____9231
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____9230
                                  us_r
                                 in
                              let as_ens =
                                let uu____9233 =
                                  let uu____9234 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____9234
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____9233
                                  us_e
                                 in
                              let req =
                                let uu____9238 =
                                  let uu____9243 =
                                    let uu____9244 =
                                      let uu____9255 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9255]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____9244
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____9243
                                   in
                                uu____9238 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____9295 =
                                  let uu____9300 =
                                    let uu____9301 =
                                      let uu____9312 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9312]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____9301
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____9300
                                   in
                                uu____9295 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____9349 =
                                let uu____9352 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____9352  in
                              let uu____9353 =
                                let uu____9354 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____9354  in
                              (uu____9349, uu____9353)))
                | uu____9357 -> failwith "Impossible"))
  
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
      (let uu____9391 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____9391
       then
         let uu____9396 = FStar_Syntax_Print.term_to_string tm  in
         let uu____9398 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____9396 uu____9398
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
        (let uu____9452 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____9452
         then
           let uu____9457 = FStar_Syntax_Print.term_to_string tm  in
           let uu____9459 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____9457
             uu____9459
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____9470 =
      let uu____9472 =
        let uu____9473 = FStar_Syntax_Subst.compress t  in
        uu____9473.FStar_Syntax_Syntax.n  in
      match uu____9472 with
      | FStar_Syntax_Syntax.Tm_app uu____9477 -> false
      | uu____9495 -> true  in
    if uu____9470
    then t
    else
      (let uu____9500 = FStar_Syntax_Util.head_and_args t  in
       match uu____9500 with
       | (head1,args) ->
           let uu____9543 =
             let uu____9545 =
               let uu____9546 = FStar_Syntax_Subst.compress head1  in
               uu____9546.FStar_Syntax_Syntax.n  in
             match uu____9545 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____9551 -> false  in
           if uu____9543
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____9583 ->
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
          ((let uu____9630 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____9630
            then
              let uu____9633 = FStar_Syntax_Print.term_to_string e  in
              let uu____9635 = FStar_Syntax_Print.term_to_string t  in
              let uu____9637 =
                let uu____9639 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____9639
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____9633 uu____9635 uu____9637
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____9652 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____9652 with
              | (formals,uu____9668) ->
                  let n_implicits =
                    let uu____9690 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____9768  ->
                              match uu____9768 with
                              | (uu____9776,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____9783 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____9783 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____9690 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____9908 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____9908 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____9922 =
                      let uu____9928 =
                        let uu____9930 = FStar_Util.string_of_int n_expected
                           in
                        let uu____9932 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____9934 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____9930 uu____9932 uu____9934
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____9928)
                       in
                    let uu____9938 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____9922 uu____9938
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_9956 =
              match uu___7_9956 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____9999 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____9999 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _10130,uu____10117)
                           when _10130 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____10163,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____10165))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____10199 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____10199 with
                            | (v1,uu____10240,g) ->
                                ((let uu____10255 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____10255
                                  then
                                    let uu____10258 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____10258
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____10268 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____10268 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____10361 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____10361))))
                       | (uu____10388,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____10425 =
                             let uu____10438 =
                               let uu____10445 =
                                 let uu____10450 = FStar_Dyn.mkdyn env  in
                                 (uu____10450, tau)  in
                               FStar_Pervasives_Native.Some uu____10445  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____10438
                              in
                           (match uu____10425 with
                            | (v1,uu____10483,g) ->
                                ((let uu____10498 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____10498
                                  then
                                    let uu____10501 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____10501
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____10511 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____10511 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____10604 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____10604))))
                       | (uu____10631,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____10679 =
                       let uu____10706 = inst_n_binders t1  in
                       aux [] uu____10706 bs1  in
                     (match uu____10679 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____10778) -> (e, torig, guard)
                           | (uu____10809,[]) when
                               let uu____10840 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____10840 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____10842 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____10870 ->
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
            | uu____10883 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____10895 =
      let uu____10899 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____10899
        (FStar_List.map
           (fun u  ->
              let uu____10911 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____10911 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____10895 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____10939 = FStar_Util.set_is_empty x  in
      if uu____10939
      then []
      else
        (let s =
           let uu____10957 =
             let uu____10960 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____10960  in
           FStar_All.pipe_right uu____10957 FStar_Util.set_elements  in
         (let uu____10976 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____10976
          then
            let uu____10981 =
              let uu____10983 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____10983  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____10981
          else ());
         (let r =
            let uu____10992 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____10992  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____11031 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____11031
                     then
                       let uu____11036 =
                         let uu____11038 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____11038
                          in
                       let uu____11042 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____11044 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____11036 uu____11042 uu____11044
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
        let uu____11074 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____11074 FStar_Util.set_elements  in
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
        | ([],uu____11113) -> generalized_univ_names
        | (uu____11120,[]) -> explicit_univ_names
        | uu____11127 ->
            let uu____11136 =
              let uu____11142 =
                let uu____11144 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____11144
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____11142)
               in
            FStar_Errors.raise_error uu____11136 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____11166 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____11166
       then
         let uu____11171 = FStar_Syntax_Print.term_to_string t  in
         let uu____11173 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____11171 uu____11173
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____11182 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____11182
        then
          let uu____11187 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____11187
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____11196 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____11196
         then
           let uu____11201 = FStar_Syntax_Print.term_to_string t  in
           let uu____11203 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____11201 uu____11203
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
        let uu____11287 =
          let uu____11289 =
            FStar_Util.for_all
              (fun uu____11303  ->
                 match uu____11303 with
                 | (uu____11313,uu____11314,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____11289  in
        if uu____11287
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____11366 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____11366
              then
                let uu____11369 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____11369
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____11376 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____11376
               then
                 let uu____11379 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____11379
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____11397 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____11397 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____11431 =
             match uu____11431 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____11468 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____11468
                   then
                     let uu____11473 =
                       let uu____11475 =
                         let uu____11479 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____11479
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____11475
                         (FStar_String.concat ", ")
                        in
                     let uu____11527 =
                       let uu____11529 =
                         let uu____11533 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____11533
                           (FStar_List.map
                              (fun u  ->
                                 let uu____11546 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____11548 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____11546
                                   uu____11548))
                          in
                       FStar_All.pipe_right uu____11529
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____11473
                       uu____11527
                   else ());
                  (let univs2 =
                     let uu____11562 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____11574 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____11574) univs1
                       uu____11562
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____11581 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____11581
                    then
                      let uu____11586 =
                        let uu____11588 =
                          let uu____11592 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____11592
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____11588
                          (FStar_String.concat ", ")
                         in
                      let uu____11640 =
                        let uu____11642 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____11656 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____11658 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____11656
                                    uu____11658))
                           in
                        FStar_All.pipe_right uu____11642
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____11586 uu____11640
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____11679 =
             let uu____11696 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____11696  in
           match uu____11679 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____11786 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____11786
                 then ()
                 else
                   (let uu____11791 = lec_hd  in
                    match uu____11791 with
                    | (lb1,uu____11799,uu____11800) ->
                        let uu____11801 = lec2  in
                        (match uu____11801 with
                         | (lb2,uu____11809,uu____11810) ->
                             let msg =
                               let uu____11813 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____11815 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____11813 uu____11815
                                in
                             let uu____11818 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____11818))
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
                 let uu____11886 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____11886
                 then ()
                 else
                   (let uu____11891 = lec_hd  in
                    match uu____11891 with
                    | (lb1,uu____11899,uu____11900) ->
                        let uu____11901 = lec2  in
                        (match uu____11901 with
                         | (lb2,uu____11909,uu____11910) ->
                             let msg =
                               let uu____11913 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____11915 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____11913 uu____11915
                                in
                             let uu____11918 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____11918))
                  in
               let lecs1 =
                 let uu____11929 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____11982 = univs_and_uvars_of_lec this_lec  in
                        match uu____11982 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____11929 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____12087 = lec_hd  in
                   match uu____12087 with
                   | (lbname,e,c) ->
                       let uu____12097 =
                         let uu____12103 =
                           let uu____12105 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____12107 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____12109 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____12105 uu____12107 uu____12109
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____12103)
                          in
                       let uu____12113 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____12097 uu____12113
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____12132 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____12132 with
                         | FStar_Pervasives_Native.Some uu____12141 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____12149 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____12153 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____12153 with
                              | (bs,kres) ->
                                  ((let uu____12197 =
                                      let uu____12198 =
                                        let uu____12201 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____12201
                                         in
                                      uu____12198.FStar_Syntax_Syntax.n  in
                                    match uu____12197 with
                                    | FStar_Syntax_Syntax.Tm_type uu____12202
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____12206 =
                                          let uu____12208 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____12208  in
                                        if uu____12206
                                        then fail1 kres
                                        else ()
                                    | uu____12213 -> fail1 kres);
                                   (let a =
                                      let uu____12215 =
                                        let uu____12218 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _12221  ->
                                             FStar_Pervasives_Native.Some
                                               _12221) uu____12218
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____12215
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____12229 ->
                                          let uu____12238 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____12238
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
                      (fun uu____12341  ->
                         match uu____12341 with
                         | (lbname,e,c) ->
                             let uu____12387 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____12448 ->
                                   let uu____12461 = (e, c)  in
                                   (match uu____12461 with
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
                                                (fun uu____12501  ->
                                                   match uu____12501 with
                                                   | (x,uu____12507) ->
                                                       let uu____12508 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____12508)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____12526 =
                                                let uu____12528 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____12528
                                                 in
                                              if uu____12526
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
                                          let uu____12537 =
                                            let uu____12538 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____12538.FStar_Syntax_Syntax.n
                                             in
                                          match uu____12537 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____12563 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____12563 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____12574 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____12578 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____12578, gen_tvars))
                                in
                             (match uu____12387 with
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
        (let uu____12725 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12725
         then
           let uu____12728 =
             let uu____12730 =
               FStar_List.map
                 (fun uu____12745  ->
                    match uu____12745 with
                    | (lb,uu____12754,uu____12755) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____12730 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____12728
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____12781  ->
                match uu____12781 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____12810 = gen env is_rec lecs  in
           match uu____12810 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____12909  ->
                       match uu____12909 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____12971 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____12971
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____13019  ->
                           match uu____13019 with
                           | (l,us,e,c,gvs) ->
                               let uu____13053 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____13055 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____13057 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____13059 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____13061 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____13053 uu____13055 uu____13057
                                 uu____13059 uu____13061))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____13106  ->
                match uu____13106 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____13150 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____13150, t, c, gvs)) univnames_lecs
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
              (let uu____13211 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____13211 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____13217 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _13220  -> FStar_Pervasives_Native.Some _13220)
                     uu____13217)
             in
          let is_var e1 =
            let uu____13228 =
              let uu____13229 = FStar_Syntax_Subst.compress e1  in
              uu____13229.FStar_Syntax_Syntax.n  in
            match uu____13228 with
            | FStar_Syntax_Syntax.Tm_name uu____13233 -> true
            | uu____13235 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1563_13256 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1563_13256.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1563_13256.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____13257 -> e2  in
          let env2 =
            let uu___1566_13259 = env1  in
            let uu____13260 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1566_13259.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1566_13259.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1566_13259.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1566_13259.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1566_13259.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1566_13259.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1566_13259.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1566_13259.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1566_13259.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1566_13259.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1566_13259.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1566_13259.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1566_13259.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1566_13259.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1566_13259.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1566_13259.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1566_13259.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____13260;
              FStar_TypeChecker_Env.is_iface =
                (uu___1566_13259.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1566_13259.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1566_13259.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1566_13259.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1566_13259.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1566_13259.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1566_13259.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1566_13259.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1566_13259.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1566_13259.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1566_13259.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1566_13259.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1566_13259.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1566_13259.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1566_13259.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1566_13259.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1566_13259.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1566_13259.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1566_13259.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1566_13259.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1566_13259.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1566_13259.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1566_13259.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1566_13259.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1566_13259.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1566_13259.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1566_13259.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1566_13259.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____13262 = check1 env2 t1 t2  in
          match uu____13262 with
          | FStar_Pervasives_Native.None  ->
              let uu____13269 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____13275 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____13269 uu____13275
          | FStar_Pervasives_Native.Some g ->
              ((let uu____13282 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____13282
                then
                  let uu____13287 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____13287
                else ());
               (let uu____13293 = decorate e t2  in (uu____13293, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____13321 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____13321
         then
           let uu____13324 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____13324
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____13338 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____13338 with
         | (c,g_c) ->
             let uu____13350 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____13350
             then
               let uu____13358 =
                 let uu____13360 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____13360  in
               (uu____13358, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____13368 =
                    let uu____13369 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____13369
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____13368
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____13370 = check_trivial_precondition env c1  in
                match uu____13370 with
                | (ct,vc,g_pre) ->
                    ((let uu____13386 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____13386
                      then
                        let uu____13391 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____13391
                      else ());
                     (let uu____13396 =
                        let uu____13398 =
                          let uu____13399 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____13399  in
                        discharge uu____13398  in
                      let uu____13400 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____13396, uu____13400)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_13434 =
        match uu___8_13434 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____13444)::[] -> f fst1
        | uu____13469 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____13481 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____13481
          (fun _13482  -> FStar_TypeChecker_Common.NonTrivial _13482)
         in
      let op_or_e e =
        let uu____13493 =
          let uu____13494 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____13494  in
        FStar_All.pipe_right uu____13493
          (fun _13497  -> FStar_TypeChecker_Common.NonTrivial _13497)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _13504  -> FStar_TypeChecker_Common.NonTrivial _13504)
         in
      let op_or_t t =
        let uu____13515 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____13515
          (fun _13518  -> FStar_TypeChecker_Common.NonTrivial _13518)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _13525  -> FStar_TypeChecker_Common.NonTrivial _13525)
         in
      let short_op_ite uu___9_13531 =
        match uu___9_13531 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____13541)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____13568)::[] ->
            let uu____13609 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____13609
              (fun _13610  -> FStar_TypeChecker_Common.NonTrivial _13610)
        | uu____13611 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____13623 =
          let uu____13631 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____13631)  in
        let uu____13639 =
          let uu____13649 =
            let uu____13657 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____13657)  in
          let uu____13665 =
            let uu____13675 =
              let uu____13683 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____13683)  in
            let uu____13691 =
              let uu____13701 =
                let uu____13709 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____13709)  in
              let uu____13717 =
                let uu____13727 =
                  let uu____13735 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____13735)  in
                [uu____13727; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____13701 :: uu____13717  in
            uu____13675 :: uu____13691  in
          uu____13649 :: uu____13665  in
        uu____13623 :: uu____13639  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____13797 =
            FStar_Util.find_map table
              (fun uu____13812  ->
                 match uu____13812 with
                 | (x,mk1) ->
                     let uu____13829 = FStar_Ident.lid_equals x lid  in
                     if uu____13829
                     then
                       let uu____13834 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____13834
                     else FStar_Pervasives_Native.None)
             in
          (match uu____13797 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____13838 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____13846 =
      let uu____13847 = FStar_Syntax_Util.un_uinst l  in
      uu____13847.FStar_Syntax_Syntax.n  in
    match uu____13846 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____13852 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____13888)::uu____13889 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____13908 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____13917,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____13918))::uu____13919 -> bs
      | uu____13937 ->
          let uu____13938 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____13938 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____13942 =
                 let uu____13943 = FStar_Syntax_Subst.compress t  in
                 uu____13943.FStar_Syntax_Syntax.n  in
               (match uu____13942 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____13947) ->
                    let uu____13968 =
                      FStar_Util.prefix_until
                        (fun uu___10_14008  ->
                           match uu___10_14008 with
                           | (uu____14016,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____14017)) ->
                               false
                           | uu____14022 -> true) bs'
                       in
                    (match uu____13968 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____14058,uu____14059) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____14131,uu____14132) ->
                         let uu____14205 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____14225  ->
                                   match uu____14225 with
                                   | (x,uu____14234) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____14205
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____14283  ->
                                     match uu____14283 with
                                     | (x,i) ->
                                         let uu____14302 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____14302, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____14313 -> bs))
  
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
            let uu____14342 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____14342
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
          let uu____14373 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____14373
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
        (let uu____14416 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____14416
         then
           ((let uu____14421 = FStar_Ident.text_of_lid lident  in
             d uu____14421);
            (let uu____14423 = FStar_Ident.text_of_lid lident  in
             let uu____14425 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____14423 uu____14425))
         else ());
        (let fv =
           let uu____14431 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____14431
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
         let uu____14443 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1723_14445 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1723_14445.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1723_14445.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1723_14445.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1723_14445.FStar_Syntax_Syntax.sigattrs)
           }), uu____14443))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_14463 =
        match uu___11_14463 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____14466 -> false  in
      let reducibility uu___12_14474 =
        match uu___12_14474 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____14481 -> false  in
      let assumption uu___13_14489 =
        match uu___13_14489 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____14493 -> false  in
      let reification uu___14_14501 =
        match uu___14_14501 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____14504 -> true
        | uu____14506 -> false  in
      let inferred uu___15_14514 =
        match uu___15_14514 with
        | FStar_Syntax_Syntax.Discriminator uu____14516 -> true
        | FStar_Syntax_Syntax.Projector uu____14518 -> true
        | FStar_Syntax_Syntax.RecordType uu____14524 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____14534 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____14547 -> false  in
      let has_eq uu___16_14555 =
        match uu___16_14555 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____14559 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____14638 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____14645 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____14656 =
        let uu____14658 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_14664  ->
                  match uu___17_14664 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____14667 -> false))
           in
        FStar_All.pipe_right uu____14658 Prims.op_Negation  in
      if uu____14656
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____14688 =
            let uu____14694 =
              let uu____14696 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____14696 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____14694)  in
          FStar_Errors.raise_error uu____14688 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____14714 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____14722 =
            let uu____14724 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____14724  in
          if uu____14722 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14734),uu____14735) ->
              ((let uu____14747 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____14747
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____14756 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____14756
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____14767 ->
              let uu____14776 =
                let uu____14778 =
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
                Prims.op_Negation uu____14778  in
              if uu____14776 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14788 ->
              let uu____14795 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14795 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14803 ->
              let uu____14810 =
                let uu____14812 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____14812  in
              if uu____14810 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14822 ->
              let uu____14823 =
                let uu____14825 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____14825  in
              if uu____14823 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14835 ->
              let uu____14836 =
                let uu____14838 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____14838  in
              if uu____14836 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14848 ->
              let uu____14861 =
                let uu____14863 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____14863  in
              if uu____14861 then err'1 () else ()
          | uu____14873 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____14912 =
          let uu____14913 = FStar_Syntax_Subst.compress t1  in
          uu____14913.FStar_Syntax_Syntax.n  in
        match uu____14912 with
        | FStar_Syntax_Syntax.Tm_arrow uu____14917 ->
            let uu____14932 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____14932 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____14965;
               FStar_Syntax_Syntax.index = uu____14966;
               FStar_Syntax_Syntax.sort = t2;_},uu____14968)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____14977) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____15003) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____15009 -> false
      
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
            FStar_TypeChecker_Env.Iota;
            FStar_TypeChecker_Env.Unascribe] env t1
           in
        let res =
          (FStar_TypeChecker_Env.non_informative env t2) || (descend env t2)
           in
        (let uu____15019 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____15019
         then
           let uu____15024 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____15024
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
              let uu____15071 =
                let uu____15072 = FStar_Syntax_Subst.compress signature  in
                uu____15072.FStar_Syntax_Syntax.n  in
              match uu____15071 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15076) when
                  (FStar_List.length bs) = (Prims.of_int (2)) ->
                  let uu____15105 = FStar_Syntax_Subst.open_binders bs  in
                  (match uu____15105 with
                   | (a,uu____15107)::(wp,uu____15109)::[] ->
                       FStar_All.pipe_right wp.FStar_Syntax_Syntax.sort
                         (FStar_Syntax_Subst.subst
                            [FStar_Syntax_Syntax.NT (a, a_tm)]))
              | uu____15138 ->
                  let uu____15139 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name signature
                     in
                  FStar_Errors.raise_error uu____15139 r
               in
            let uu____15145 =
              let uu____15158 =
                let uu____15160 = FStar_Range.string_of_range r  in
                FStar_Util.format2 "implicit for wp of %s at %s"
                  eff_name.FStar_Ident.str uu____15160
                 in
              new_implicit_var uu____15158 r env wp_sort  in
            match uu____15145 with
            | (wp_uvar,uu____15168,g_wp_uvar) ->
                let eff_c =
                  let uu____15183 =
                    let uu____15184 =
                      let uu____15195 =
                        FStar_All.pipe_right wp_uvar
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____15195]  in
                    {
                      FStar_Syntax_Syntax.comp_univs = [u];
                      FStar_Syntax_Syntax.effect_name = eff_name;
                      FStar_Syntax_Syntax.result_typ = a_tm;
                      FStar_Syntax_Syntax.effect_args = uu____15184;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____15183  in
                let uu____15228 =
                  let uu____15229 =
                    let uu____15236 =
                      let uu____15237 =
                        let uu____15252 =
                          let uu____15261 =
                            FStar_Syntax_Syntax.null_binder
                              FStar_Syntax_Syntax.t_unit
                             in
                          [uu____15261]  in
                        (uu____15252, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____15237  in
                    FStar_Syntax_Syntax.mk uu____15236  in
                  uu____15229 FStar_Pervasives_Native.None r  in
                (uu____15228, g_wp_uvar)
  
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
                  let uu____15340 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____15340 r  in
                let uu____15350 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____15350 with
                | (uu____15359,signature) ->
                    let uu____15361 =
                      let uu____15362 = FStar_Syntax_Subst.compress signature
                         in
                      uu____15362.FStar_Syntax_Syntax.n  in
                    (match uu____15361 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15370) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____15418 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____15433 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____15435 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____15433 eff_name.FStar_Ident.str
                                       uu____15435) r
                                 in
                              (match uu____15418 with
                               | (is,g) ->
                                   let repr =
                                     let uu____15449 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____15449
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____15458 =
                                     let uu____15459 =
                                       let uu____15464 =
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
                                         uu____15464
                                        in
                                     uu____15459 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____15458, g))
                          | uu____15473 -> fail1 signature)
                     | uu____15474 -> fail1 signature)
  
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
            let uu____15505 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____15505
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
              let uu____15550 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____15550 with
              | (uu____15555,sig_tm) ->
                  let fail1 t =
                    let uu____15563 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____15563 r  in
                  let uu____15569 =
                    let uu____15570 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____15570.FStar_Syntax_Syntax.n  in
                  (match uu____15569 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15574) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____15597)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____15619 -> fail1 sig_tm)
                   | uu____15620 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.lift_comp_t)
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____15641 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____15641
           then
             let uu____15646 = FStar_Syntax_Print.comp_to_string c  in
             let uu____15648 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____15646 uu____15648
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____15678 =
               let uu____15679 =
                 let uu____15685 =
                   let uu____15687 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____15689 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____15687 uu____15689
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15685)  in
               FStar_Errors.raise_error uu____15679 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____15701,uu____15702::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____15770 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____15775,c1) ->
                    let uu____15797 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____15797
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____15832 -> err ())
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____15834 =
             let uu____15845 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____15846 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____15845, (ct.FStar_Syntax_Syntax.result_typ), uu____15846)
              in
           match uu____15834 with
           | (u,a,c_is) ->
               let uu____15894 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____15894 with
                | (uu____15903,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____15914 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____15916 = FStar_Ident.string_of_lid tgt  in
                      let uu____15918 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____15914 uu____15916 s uu____15918
                       in
                    let uu____15921 =
                      let uu____15954 =
                        let uu____15955 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____15955.FStar_Syntax_Syntax.n  in
                      match uu____15954 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____16019 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____16019 with
                           | (a_b::bs1,c2) ->
                               let uu____16079 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____16141 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16079, uu____16141))
                      | uu____16168 ->
                          let uu____16169 =
                            let uu____16175 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____16175)
                             in
                          FStar_Errors.raise_error uu____16169 r
                       in
                    (match uu____15921 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____16293 =
                           let uu____16300 =
                             let uu____16301 =
                               let uu____16302 =
                                 let uu____16309 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____16309, a)  in
                               FStar_Syntax_Syntax.NT uu____16302  in
                             [uu____16301]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____16300
                             (fun b  ->
                                let uu____16326 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____16328 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____16330 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____16332 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____16326 uu____16328 uu____16330
                                  uu____16332) r
                            in
                         (match uu____16293 with
                          | (rest_bs_uvars,g) ->
                              let substs =
                                FStar_List.map2
                                  (fun b  ->
                                     fun t  ->
                                       let uu____16369 =
                                         let uu____16376 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____16376, t)  in
                                       FStar_Syntax_Syntax.NT uu____16369)
                                  (a_b :: rest_bs) (a :: rest_bs_uvars)
                                 in
                              let guard_f =
                                let f_sort =
                                  let uu____16395 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                      (FStar_Syntax_Subst.subst substs)
                                     in
                                  FStar_All.pipe_right uu____16395
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____16401 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  effect_args_from_repr f_sort uu____16401
                                   in
                                FStar_List.fold_left2
                                  (fun g1  ->
                                     fun i1  ->
                                       fun i2  ->
                                         let uu____16410 =
                                           FStar_TypeChecker_Rel.teq env i1
                                             i2
                                            in
                                         FStar_TypeChecker_Env.conj_guard g1
                                           uu____16410)
                                  FStar_TypeChecker_Env.trivial_guard c_is
                                  f_sort_is
                                 in
                              let is =
                                let uu____16414 =
                                  FStar_TypeChecker_Env.is_layered_effect env
                                    tgt
                                   in
                                effect_args_from_repr
                                  lift_ct.FStar_Syntax_Syntax.result_typ
                                  uu____16414
                                 in
                              let c1 =
                                let uu____16417 =
                                  let uu____16418 =
                                    let uu____16429 =
                                      FStar_All.pipe_right is
                                        (FStar_List.map
                                           (FStar_Syntax_Subst.subst substs))
                                       in
                                    FStar_All.pipe_right uu____16429
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.as_arg)
                                     in
                                  {
                                    FStar_Syntax_Syntax.comp_univs =
                                      (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                    FStar_Syntax_Syntax.effect_name = tgt;
                                    FStar_Syntax_Syntax.result_typ = a;
                                    FStar_Syntax_Syntax.effect_args =
                                      uu____16418;
                                    FStar_Syntax_Syntax.flags =
                                      (ct.FStar_Syntax_Syntax.flags)
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____16417  in
                              ((let uu____16449 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____16449
                                then
                                  let uu____16454 =
                                    FStar_Syntax_Print.comp_to_string c1  in
                                  FStar_Util.print1 "} Lifted comp: %s\n"
                                    uu____16454
                                else ());
                               (let uu____16459 =
                                  FStar_TypeChecker_Env.conj_guard g guard_f
                                   in
                                (c1, uu____16459)))))))
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____16478 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____16478 with
        | (uu____16483,t) ->
            let err n1 =
              let uu____16493 =
                let uu____16499 =
                  let uu____16501 = FStar_Ident.string_of_lid datacon  in
                  let uu____16503 = FStar_Util.string_of_int n1  in
                  let uu____16505 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____16501 uu____16503 uu____16505
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____16499)
                 in
              let uu____16509 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____16493 uu____16509  in
            let uu____16510 =
              let uu____16511 = FStar_Syntax_Subst.compress t  in
              uu____16511.FStar_Syntax_Syntax.n  in
            (match uu____16510 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16515) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____16570  ->
                           match uu____16570 with
                           | (uu____16578,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____16587 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____16619 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____16619
                      FStar_Pervasives_Native.fst)
             | uu____16630 -> err Prims.int_zero)
  