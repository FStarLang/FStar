open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____143 = FStar_TypeChecker_Env.get_range env  in
      let uu____144 =
        FStar_TypeChecker_Err.failed_to_prove_specification errs  in
      FStar_Errors.log_issue uu____143 uu____144
  
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
        let uu____465 =
          let uu____467 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____467  in
        if uu____465
        then g
        else
          (let uu____478 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____530  ->
                     match uu____530 with
                     | (uu____537,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____478 with
           | (solve_now,defer) ->
               ((let uu____576 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____576
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____593  ->
                         match uu____593 with
                         | (s,p) ->
                             let uu____603 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____603)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____618  ->
                         match uu____618 with
                         | (s,p) ->
                             let uu____628 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____628) defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___46_644 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___46_644.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___46_644.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___46_644.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___49_662 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___49_662.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___49_662.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___49_662.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____701 =
        let uu____703 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____703  in
      if uu____701
      then
        let us =
          let uu____716 =
            let uu____720 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____720
             in
          FStar_All.pipe_right uu____716 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____771 =
            let uu____777 =
              let uu____779 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____779
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____777)  in
          FStar_Errors.log_issue r uu____771);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____867  ->
      match uu____867 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____943;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____945;
          FStar_Syntax_Syntax.lbpos = uu____946;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____1027 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 e  in
               (match uu____1027 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____1231) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____1246) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1353) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____1453 = FStar_Options.ml_ish ()  in
                                if uu____1453
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____1508 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____1508
                            then
                              let uu____1511 = FStar_Range.string_of_range r
                                 in
                              let uu____1513 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____1511 uu____1513
                            else ());
                           FStar_Util.Inl t2)
                      | uu____1526 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____1544 = aux e1  in
                      match uu____1544 with
                      | FStar_Util.Inr c ->
                          let uu____1574 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____1574
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____1583 =
                               let uu____1589 =
                                 let uu____1591 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____1591
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____1589)
                                in
                             FStar_Errors.raise_error uu____1583 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____1622 ->
               let uu____1623 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1623 with
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
    let pat_as_arg uu____1746 =
      match uu____1746 with
      | (p,i) ->
          let uu____1775 = decorated_pattern_as_term p  in
          (match uu____1775 with
           | (vars,te) ->
               let uu____1834 =
                 let uu____1843 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____1843)  in
               (vars, uu____1834))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____1879 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____1879)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____1910 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____1910)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____1946 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____1946)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2008 =
          let uu____2036 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____2036 FStar_List.unzip  in
        (match uu____2008 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____2265 =
               let uu____2274 =
                 let uu____2275 =
                   let uu____2300 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____2300, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____2275  in
               mk1 uu____2274  in
             (vars1, uu____2265))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____2404,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____2422,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____2449 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____2476 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp
       in
    FStar_All.pipe_right uu____2476 comp_univ_opt
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____2567)::[] -> wp
      | uu____2608 ->
          let uu____2623 =
            let uu____2625 =
              let uu____2627 =
                FStar_List.map
                  (fun uu____2645  ->
                     match uu____2645 with
                     | (x,uu____2658) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____2627 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____2625
             in
          failwith uu____2623
       in
    let uu____2681 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____2681, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____2739 = destruct_comp c  in
        match uu____2739 with
        | (u,uu____2760,wp) ->
            let uu____2778 =
              let uu____2793 =
                let uu____2806 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____2806  in
              [uu____2793]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____2778;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2983 =
          let uu____3004 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____3013 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____3004 uu____3013  in
        match uu____2983 with | (m,uu____3027,uu____3028) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____3217 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____3217
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
        let uu____3457 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____3457 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____3641 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____3641 with
             | (a,kwp) ->
                 let uu____3744 = destruct_comp m1  in
                 let uu____3759 = destruct_comp m2  in
                 ((md, a, kwp), uu____3744, uu____3759))
  
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
            let uu____4202 =
              let uu____4213 =
                let uu____4228 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4228]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4213;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4202
  
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
          let uu____4396 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4396
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
      let uu____4440 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4440
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4451  ->
           let uu____4452 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4452)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4476 =
      let uu____4477 = FStar_Syntax_Subst.compress t  in
      uu____4477.FStar_Syntax_Syntax.n  in
    match uu____4476 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4489 -> true
    | uu____4514 -> false
  
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
              let uu____4728 =
                let uu____4730 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4730  in
              if uu____4728
              then f
              else (let uu____4741 = reason1 ()  in label uu____4741 r f)
  
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
            let uu___243_4782 = g  in
            let uu____4791 =
              let uu____4792 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4792  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4791;
              FStar_TypeChecker_Env.deferred =
                (uu___243_4782.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___243_4782.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___243_4782.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4951 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4951
        then c
        else
          (let uu____4960 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4960
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____5119 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____5119]  in
                       let us =
                         let uu____5156 =
                           let uu____5159 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____5159]  in
                         u_res :: uu____5156  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____5184 =
                         let uu____5189 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____5198 =
                           let uu____5199 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____5212 =
                             let uu____5227 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____5240 =
                               let uu____5255 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____5255]  in
                             uu____5227 :: uu____5240  in
                           uu____5199 :: uu____5212  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____5189 uu____5198
                          in
                       uu____5184 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____5327 = destruct_comp c1  in
              match uu____5327 with
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
          (fun uu____5581  ->
             let uu____5582 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____5582)
  
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
              ({ FStar_Syntax_Syntax.ppname = uu____5767;
                 FStar_Syntax_Syntax.index = uu____5768;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____5770;
                     FStar_Syntax_Syntax.vars = uu____5771;_};_},uu____5772)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____5812 -> c
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___0_5840  ->
            match uu___0_5840 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____5843 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____6000 =
            let uu____6011 =
              FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____6011 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____6000
            (fun c  ->
               (let uu____6119 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____6119) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____6127 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____6127)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____6150 = FStar_Syntax_Util.head_and_args' e  in
                match uu____6150 with
                | (head1,uu____6175) ->
                    let uu____6212 =
                      let uu____6213 = FStar_Syntax_Util.un_uinst head1  in
                      uu____6213.FStar_Syntax_Syntax.n  in
                    (match uu____6212 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____6229 =
                           let uu____6231 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____6231
                            in
                         Prims.op_Negation uu____6229
                     | uu____6240 -> true)))
              &&
              (let uu____6243 = should_not_inline_lc lc  in
               Prims.op_Negation uu____6243)
  
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
            let uu____6407 =
              let uu____6409 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____6409  in
            if uu____6407
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____6420 = FStar_Syntax_Util.is_unit t  in
               if uu____6420
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
                    let uu____6481 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____6481
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____6490 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____6490 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____6548 =
                             let uu____6557 =
                               let uu____6562 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____6571 =
                                 let uu____6572 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____6585 =
                                   let uu____6600 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____6600]  in
                                 uu____6572 :: uu____6585  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____6562
                                 uu____6571
                                in
                             uu____6557 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____6548)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____6650 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____6650
           then
             let uu____6655 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____6657 = FStar_Syntax_Print.term_to_string v1  in
             let uu____6659 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____6655 uu____6657 uu____6659
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____6676 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_6682  ->
              match uu___1_6682 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____6685 -> false))
       in
    if uu____6676
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_6697  ->
              match uu___2_6697 with
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
        let uu____6849 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____6849
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____6869 = destruct_comp c1  in
           match uu____6869 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____6959 =
                   let uu____6964 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____6973 =
                     let uu____6974 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____6987 =
                       let uu____7002 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____7015 =
                         let uu____7030 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____7030]  in
                       uu____7002 :: uu____7015  in
                     uu____6974 :: uu____6987  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____6964 uu____6973  in
                 uu____6959 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____7091 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____7091)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____7259 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____7269 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____7269
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____7287 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____7287 weaken
  
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
               let uu____7477 = destruct_comp c1  in
               match uu____7477 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____7567 =
                       let uu____7572 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____7581 =
                         let uu____7582 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____7595 =
                           let uu____7610 =
                             let uu____7623 =
                               let uu____7632 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____7632 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____7623
                              in
                           let uu____7649 =
                             let uu____7664 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____7664]  in
                           uu____7610 :: uu____7649  in
                         uu____7582 :: uu____7595  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____7572 uu____7581
                        in
                     uu____7567 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos
                      in
                   mk_comp md u_res_t res_t wp1 flags)
  
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
            let uu____7934 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____7934
            then (lc, g0)
            else
              (let flags =
                 let uu____7970 =
                   let uu____7978 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____7978
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____7970 with
                 | (maybe_trivial_post,flags) ->
                     let uu____8008 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___3_8016  ->
                               match uu___3_8016 with
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
                               | uu____8019 -> []))
                        in
                     FStar_List.append flags uu____8008
                  in
               let strengthen uu____8029 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____8055 = FStar_TypeChecker_Env.guard_form g01  in
                    match uu____8055 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____8066 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____8066
                          then
                            let uu____8070 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____8072 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____8070 uu____8072
                          else ());
                         strengthen_comp env reason c f flags))
                  in
               let uu____8077 =
                 let uu____8094 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____8094
                   lc.FStar_Syntax_Syntax.res_typ flags strengthen
                  in
               (uu____8077,
                 (let uu___398_8116 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___398_8116.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___398_8116.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___398_8116.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_8149  ->
            match uu___4_8149 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____8153 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____8318 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____8318
          then e
          else
            (let uu____8329 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____8332 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____8332)
                in
             if uu____8329
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
          fun uu____8471  ->
            match uu____8471 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____8599 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____8599 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____8652 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____8652
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____8662 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____8662
                       then
                         let uu____8667 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____8667
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____8674 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____8674
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____8683 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____8683
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____8690 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____8690
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____8706 =
                  let uu____8707 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____8707
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
                       (fun uu____8744  ->
                          let uu____8745 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____8747 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____8767 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____8745 uu____8747 uu____8767);
                     (let aux uu____8789 =
                        let uu____8790 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____8790
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____8842 ->
                              let uu____8853 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____8853
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____8901 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____8901
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____8966 =
                        let uu____8967 =
                          let uu____8969 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____8969  in
                        if uu____8967
                        then
                          let uu____8995 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____8995
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____9030 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____9030))
                        else
                          (let uu____9049 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____9049
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___464_9127 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___464_9127.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___464_9127.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____9138 =
                                 let uu____9148 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____9148, reason)  in
                               FStar_Util.Inl uu____9138  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____9240 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____9240
                                   (close1 x "c1 Tot")
                             | (uu____9287,FStar_Pervasives_Native.Some x) ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____9341,uu____9342) -> aux ()
                           else
                             (let uu____9375 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____9375
                              then
                                let uu____9392 =
                                  let uu____9402 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____9402, "both GTot")  in
                                FStar_Util.Inl uu____9392
                              else aux ()))
                         in
                      let uu____9429 = try_simplify ()  in
                      match uu____9429 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____9475  ->
                                let uu____9476 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____9476);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____9494  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____9546 = lift_and_destruct env c11 c21
                                 in
                              match uu____9546 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____9788 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____9788]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____9833 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____9833]
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
                                    let uu____9930 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____9943 =
                                      let uu____9958 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____9971 =
                                        let uu____9986 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____9999 =
                                          let uu____10014 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____10027 =
                                            let uu____10042 =
                                              let uu____10055 = mk_lam wp2
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____10055
                                               in
                                            [uu____10042]  in
                                          uu____10014 :: uu____10027  in
                                        uu____9986 :: uu____9999  in
                                      uu____9958 :: uu____9971  in
                                    uu____9930 :: uu____9943  in
                                  let wp =
                                    let uu____10147 =
                                      let uu____10152 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____10152 wp_args
                                       in
                                    uu____10147 FStar_Pervasives_Native.None
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
                              let uu____10233 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____10233 with
                              | (m,uu____10259,lift2) ->
                                  let c23 =
                                    let uu____10298 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____10298
                                     in
                                  let uu____10309 = destruct_comp c12  in
                                  (match uu____10309 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____10399 =
                                           let uu____10404 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____10413 =
                                             let uu____10414 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____10427 =
                                               let uu____10442 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____10442]  in
                                             uu____10414 :: uu____10427  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____10404 uu____10413
                                            in
                                         uu____10399
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
                            let uu____10506 = destruct_comp c1_typ  in
                            match uu____10506 with
                            | (u_res_t1,res_t1,uu____10527) ->
                                let uu____10544 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____10544
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____10585 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____10585
                                   then
                                     (debug1
                                        (fun uu____10599  ->
                                           let uu____10600 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____10602 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____10600 uu____10602);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____10627 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____10630 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____10630)
                                         in
                                      if uu____10627
                                      then
                                        let e1' =
                                          let uu____10671 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____10671
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____10687  ->
                                              let uu____10688 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____10690 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____10688 uu____10690);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____10722  ->
                                              let uu____10723 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____10725 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____10723 uu____10725);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____10757 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____10757
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
      | uu____10807 -> g2
  
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
            (let uu____10983 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____10983)
           in
        let flags =
          if should_return1
          then
            let uu____10991 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____10991
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____11011 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____11023 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____11023
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____11041 =
              let uu____11043 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____11043  in
            (if uu____11041
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___583_11074 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___583_11074.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___583_11074.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___583_11074.FStar_Syntax_Syntax.effect_args);
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
               let uu____11157 =
                 let uu____11166 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____11166
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                 uu____11157
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____11213 =
               let uu____11222 =
                 let uu____11239 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____11239
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____11222  in
             FStar_Syntax_Util.comp_set_flags uu____11213 flags)
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
            fun uu____11401  ->
              match uu____11401 with
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
                    let uu____11557 =
                      ((let uu____11561 = is_pure_or_ghost_effect env eff1
                           in
                        Prims.op_Negation uu____11561) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____11557
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____11720 =
        let uu____11729 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____11729  in
      FStar_Syntax_Syntax.fvar uu____11720 FStar_Syntax_Syntax.delta_constant
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
               fun uu____11991  ->
                 match uu____11991 with
                 | (uu____12029,eff_label,uu____12031,uu____12032) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____12077 =
          let uu____12085 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____12155  ->
                    match uu____12155 with
                    | (uu____12186,uu____12187,flags,uu____12189) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_12238  ->
                                match uu___5_12238 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____12241 -> false))))
             in
          if uu____12085
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____12077 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____12286 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____12288 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____12288
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____12409 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____12410 =
                     let uu____12415 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____12424 =
                       let uu____12425 = FStar_Syntax_Syntax.as_arg res_t1
                          in
                       let uu____12438 =
                         let uu____12453 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____12466 =
                           let uu____12481 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____12494 =
                             let uu____12509 =
                               FStar_Syntax_Syntax.as_arg wp_e  in
                             [uu____12509]  in
                           uu____12481 :: uu____12494  in
                         uu____12453 :: uu____12466  in
                       uu____12425 :: uu____12438  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____12415 uu____12424
                      in
                   uu____12410 FStar_Pervasives_Native.None uu____12409  in
                 let default_case =
                   let post_k =
                     let uu____12602 =
                       let uu____12616 =
                         FStar_Syntax_Syntax.null_binder res_t  in
                       [uu____12616]  in
                     let uu____12650 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____12602 uu____12650  in
                   let kwp =
                     let uu____12672 =
                       let uu____12686 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____12686]  in
                     let uu____12720 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____12672 uu____12720  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____12753 =
                       let uu____12754 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____12754]  in
                     let uu____12788 =
                       let uu____12799 =
                         let uu____12814 =
                           FStar_TypeChecker_Env.get_range env  in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____12814
                          in
                       let uu____12815 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____12799 uu____12815  in
                     FStar_Syntax_Util.abs uu____12753 uu____12788
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
                   let uu____12938 =
                     should_not_inline_whole_match ||
                       (let uu____12941 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____12941)
                      in
                   if uu____12938 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____13016  ->
                        fun celse  ->
                          match uu____13016 with
                          | (g,eff_label,uu____13057,cthen) ->
                              let uu____13103 =
                                let uu____13173 =
                                  let uu____13182 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____13182
                                   in
                                lift_and_destruct env uu____13173 celse  in
                              (match uu____13103 with
                               | ((md,uu____13204,uu____13205),(uu____13206,uu____13207,wp_then),
                                  (uu____13209,uu____13210,wp_else)) ->
                                   let uu____13365 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____13365 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____13408::[] -> comp
                 | uu____13499 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____13584 = destruct_comp comp1  in
                     (match uu____13584 with
                      | (uu____13603,uu____13604,wp) ->
                          let wp1 =
                            let uu____13633 =
                              let uu____13638 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____13647 =
                                let uu____13648 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____13661 =
                                  let uu____13676 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____13676]  in
                                uu____13648 :: uu____13661  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____13638
                                uu____13647
                               in
                            uu____13633 FStar_Pervasives_Native.None
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
          let uu____13914 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____13914 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____13962 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____13972 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____13962 uu____13972
              else
                (let uu____13993 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____14003 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____13993 uu____14003)
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
          let uu____14184 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____14184
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____14211 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____14211
        then u_res
        else
          (let is_total =
             let uu____14218 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____14218
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____14229 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____14229 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14240 =
                    let uu____14246 =
                      let uu____14248 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____14248
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____14246)
                     in
                  FStar_Errors.raise_error uu____14240
                    c.FStar_Syntax_Syntax.pos
              | FStar_Pervasives_Native.Some tm ->
                  env.FStar_TypeChecker_Env.universe_of env tm))
  
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
               let uu____14493 =
                 let uu____14494 = FStar_Syntax_Subst.compress t2  in
                 uu____14494.FStar_Syntax_Syntax.n  in
               match uu____14493 with
               | FStar_Syntax_Syntax.Tm_type uu____14506 -> true
               | uu____14508 -> false  in
             let uu____14510 =
               let uu____14511 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____14511.FStar_Syntax_Syntax.n  in
             match uu____14510 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____14542 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____14564 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____14564
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____14591 =
                     let uu____14592 =
                       let uu____14609 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____14609
                        in
                     (FStar_Pervasives_Native.None, uu____14592)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____14591
                    in
                 let e1 =
                   let uu____14665 =
                     let uu____14670 =
                       let uu____14671 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____14671]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____14670  in
                   uu____14665 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____14720 -> (e, lc))
  
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
          (let uu____14939 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____14939
           then
             let uu____14942 = FStar_Syntax_Print.term_to_string e  in
             let uu____14944 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____14946 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____14942 uu____14944 uu____14946
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____14956 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____14956 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____15061 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____15115 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____15115, false)
             else
               (let uu____15133 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____15133, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____15170) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____15206 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____15206
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___739_15258 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___739_15258.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___739_15258.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___739_15258.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____15293 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____15293 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____15325 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t  in
                      let uu____15368 =
                        let uu____15370 = FStar_Syntax_Util.eq_tm t res_t  in
                        uu____15370 = FStar_Syntax_Util.Equal  in
                      if uu____15368
                      then
                        ((let uu____15377 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____15377
                          then
                            let uu____15381 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____15383 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____15381 uu____15383
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
                           | FStar_Syntax_Syntax.Tm_refine uu____15402 ->
                               true
                           | uu____15419 -> false  in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t
                              in
                           let cret =
                             let uu____15446 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             return_value env (comp_univ_opt c) res_t
                               uu____15446
                              in
                           let lc1 =
                             let uu____15472 =
                               FStar_Syntax_Util.lcomp_of_comp c  in
                             let uu____15489 =
                               let uu____15490 =
                                 FStar_Syntax_Util.lcomp_of_comp cret  in
                               ((FStar_Pervasives_Native.Some x),
                                 uu____15490)
                                in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____15472
                               uu____15489
                              in
                           ((let uu____15532 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____15532
                             then
                               let uu____15536 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____15538 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               let uu____15540 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____15542 =
                                 FStar_Syntax_Print.lcomp_to_string lc1  in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____15536 uu____15538 uu____15540
                                 uu____15542
                             else ());
                            (let uu____15547 =
                               FStar_Syntax_Syntax.lcomp_comp lc1  in
                             set_result_typ1 uu____15547))
                         else
                           ((let uu____15559 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____15559
                             then
                               let uu____15563 =
                                 FStar_Syntax_Print.term_to_string res_t  in
                               let uu____15565 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____15563 uu____15565
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
                      let uu___771_15617 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___771_15617.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___771_15617.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___771_15617.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____15635 =
                      let uu____15636 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____15636
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding true;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____15655 =
                           let uu____15656 = FStar_Syntax_Subst.compress f1
                              in
                           uu____15656.FStar_Syntax_Syntax.n  in
                         match uu____15655 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____15671,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15673;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15674;_},uu____15675)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___787_15752 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___787_15752.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___787_15752.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___787_15752.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____15769 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____15780 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____15780
                               then
                                 let uu____15784 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____15786 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____15788 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____15790 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____15784 uu____15786 uu____15788
                                   uu____15790
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
                                   let uu____15841 =
                                     let uu____15846 =
                                       let uu____15847 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____15847]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____15846
                                      in
                                   uu____15841 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____15886 =
                                 let uu____15903 =
                                   FStar_All.pipe_left
                                     (fun _15924  ->
                                        FStar_Pervasives_Native.Some _15924)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____15925 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____16034 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____16051 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____15903
                                   uu____15925 e uu____16034 uu____16051
                                  in
                               match uu____15886 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___803_16105 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___803_16105.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___803_16105.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____16133 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____16133
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____16184 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____16184
                                     then
                                       let uu____16188 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____16188
                                     else ());
                                    c2))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___6_16201  ->
                              match uu___6_16201 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____16204 -> []))
                       in
                    let lc1 =
                      let uu____16222 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____16222 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___817_16240 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___817_16240.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___817_16240.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___817_16240.FStar_TypeChecker_Env.implicits)
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
        let uu____16454 =
          let uu____16465 =
            let uu____16470 =
              let uu____16471 =
                let uu____16484 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____16484  in
              [uu____16471]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____16470  in
          uu____16465 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____16454  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding false;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____16536 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____16536
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____16583 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____16611 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____16645 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____16645
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____16677)::(ens,uu____16679)::uu____16680 ->
                    let uu____16751 =
                      let uu____16758 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____16758  in
                    let uu____16771 =
                      let uu____16780 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____16780  in
                    (uu____16751, uu____16771)
                | uu____16807 ->
                    let uu____16822 =
                      let uu____16828 =
                        let uu____16830 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____16830
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____16828)
                       in
                    FStar_Errors.raise_error uu____16822
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____16876)::uu____16877 ->
                    let uu____16920 =
                      let uu____16929 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____16929
                       in
                    (match uu____16920 with
                     | (us_r,uu____16985) ->
                         let uu____16994 =
                           let uu____17003 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____17003
                            in
                         (match uu____16994 with
                          | (us_e,uu____17059) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____17078 =
                                  let uu____17087 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____17087
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____17078
                                  us_r
                                 in
                              let as_ens =
                                let uu____17105 =
                                  let uu____17114 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____17114
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____17105
                                  us_e
                                 in
                              let req =
                                let uu____17134 =
                                  let uu____17139 =
                                    let uu____17140 =
                                      let uu____17155 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____17155]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____17140
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____17139
                                   in
                                uu____17134 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____17223 =
                                  let uu____17228 =
                                    let uu____17229 =
                                      let uu____17244 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____17244]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____17229
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____17228
                                   in
                                uu____17223 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____17301 =
                                let uu____17308 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____17308  in
                              let uu____17321 =
                                let uu____17330 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____17330  in
                              (uu____17301, uu____17321)))
                | uu____17349 -> failwith "Impossible"))
  
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
          FStar_TypeChecker_Env.Eager_unfolding false;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses] env tm
         in
      (let uu____17536 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____17536
       then
         let uu____17541 = FStar_Syntax_Print.term_to_string tm  in
         let uu____17543 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____17541
           uu____17543
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
            FStar_TypeChecker_Env.Eager_unfolding false;
            FStar_TypeChecker_Env.EraseUniverses;
            FStar_TypeChecker_Env.AllowUnboundUniverses] env tm
           in
        (let uu____17754 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____17754
         then
           let uu____17759 = FStar_Syntax_Print.term_to_string tm  in
           let uu____17761 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____17759
             uu____17761
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____17788 =
      let uu____17790 =
        let uu____17791 = FStar_Syntax_Subst.compress t  in
        uu____17791.FStar_Syntax_Syntax.n  in
      match uu____17790 with
      | FStar_Syntax_Syntax.Tm_app uu____17803 -> false
      | uu____17829 -> true  in
    if uu____17788
    then t
    else
      (let uu____17838 = FStar_Syntax_Util.head_and_args t  in
       match uu____17838 with
       | (head1,args) ->
           let uu____17909 =
             let uu____17911 =
               let uu____17912 = FStar_Syntax_Subst.compress head1  in
               uu____17912.FStar_Syntax_Syntax.n  in
             match uu____17911 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____17925 -> false  in
           if uu____17909
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____17981 ->
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
          ((let uu____18204 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____18204
            then
              let uu____18207 = FStar_Syntax_Print.term_to_string e  in
              let uu____18209 = FStar_Syntax_Print.term_to_string t  in
              let uu____18211 =
                let uu____18213 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____18213
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____18207 uu____18209 uu____18211
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____18250 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____18250 with
              | (formals,uu____18275) ->
                  let n_implicits =
                    let uu____18315 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____18433  ->
                              match uu____18433 with
                              | (uu____18446,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____18463 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____18463 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____18315 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____18666 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____18666 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____18696 =
                      let uu____18702 =
                        let uu____18704 = FStar_Util.string_of_int n_expected
                           in
                        let uu____18706 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____18708 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____18704 uu____18706 uu____18708
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____18702)
                       in
                    let uu____18712 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____18696 uu____18712
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_18730 =
              match uu___7_18730 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____18811 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____18811 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _19012,uu____18994)
                           when _19012 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____19067,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____19069))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____19136 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____19136 with
                            | (v1,uu____19206,g) ->
                                ((let uu____19253 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____19253
                                  then
                                    let uu____19256 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____19256
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____19275 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____19275 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____19420 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____19420))))
                       | (uu____19476,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____19550 =
                             let uu____19579 =
                               let uu____19590 =
                                 let uu____19599 = FStar_Dyn.mkdyn env  in
                                 (uu____19599, tau)  in
                               FStar_Pervasives_Native.Some uu____19590  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____19579
                              in
                           (match uu____19550 with
                            | (v1,uu____19707,g) ->
                                ((let uu____19754 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____19754
                                  then
                                    let uu____19757 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____19757
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____19776 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____19776 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____19921 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____19921))))
                       | (uu____19977,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____20052 =
                       let uu____20092 = inst_n_binders t1  in
                       aux [] uu____20092 bs1  in
                     (match uu____20052 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____20223) -> (e, torig, guard)
                           | (uu____20284,[]) when
                               let uu____20333 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____20333 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____20347 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____20401 ->
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
            | uu____20447 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____20471 =
      let uu____20475 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____20475
        (FStar_List.map
           (fun u  ->
              let uu____20487 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____20487 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____20471 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____20627 = FStar_Util.set_is_empty x  in
      if uu____20627
      then []
      else
        (let s =
           let uu____20651 =
             let uu____20654 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____20654  in
           FStar_All.pipe_right uu____20651 FStar_Util.set_elements  in
         (let uu____20672 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____20672
          then
            let uu____20677 =
              let uu____20679 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____20679  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____20677
          else ());
         (let r =
            let uu____20688 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____20688  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____20743 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____20743
                     then
                       let uu____20748 =
                         let uu____20750 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____20750
                          in
                       let uu____20754 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____20756 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____20748 uu____20754 uu____20756
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
        let uu____20912 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____20912 FStar_Util.set_elements  in
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
        | ([],uu____20985) -> generalized_univ_names
        | (uu____21000,[]) -> explicit_univ_names
        | uu____21015 ->
            let uu____21028 =
              let uu____21034 =
                let uu____21036 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____21036
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____21034)
               in
            FStar_Errors.raise_error uu____21028 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____21186 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____21186
       then
         let uu____21191 = FStar_Syntax_Print.term_to_string t  in
         let uu____21193 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____21191 uu____21193
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____21202 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____21202
        then
          let uu____21207 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____21207
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____21218 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____21218
         then
           let uu____21223 = FStar_Syntax_Print.term_to_string t  in
           let uu____21225 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____21223 uu____21225
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
        let uu____21477 =
          let uu____21479 =
            FStar_Util.for_all
              (fun uu____21501  ->
                 match uu____21501 with
                 | (uu____21519,uu____21520,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____21479  in
        if uu____21477
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____21620 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____21620
              then
                let uu____21623 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____21623
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____21638 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____21638
               then
                 let uu____21641 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____21641
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____21683 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____21683 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____21781 =
             match uu____21781 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____21882 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____21882
                   then
                     let uu____21887 =
                       let uu____21889 =
                         let uu____21893 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____21893
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____21889
                         (FStar_String.concat ", ")
                        in
                     let uu____21949 =
                       let uu____21951 =
                         let uu____21955 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____21955
                           (FStar_List.map
                              (fun u  ->
                                 let uu____22008 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____22010 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____22008
                                   uu____22010))
                          in
                       FStar_All.pipe_right uu____21951
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____21887
                       uu____21949
                   else ());
                  (let univs2 =
                     let uu____22024 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____22068 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____22068) univs1
                       uu____22024
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____22083 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____22083
                    then
                      let uu____22088 =
                        let uu____22090 =
                          let uu____22094 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____22094
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____22090
                          (FStar_String.concat ", ")
                         in
                      let uu____22150 =
                        let uu____22152 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____22190 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____22192 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____22190
                                    uu____22192))
                           in
                        FStar_All.pipe_right uu____22152
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____22088 uu____22150
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____22237 =
             let uu____22270 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____22270  in
           match uu____22237 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____22434 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____22434
                 then ()
                 else
                   (let uu____22439 = lec_hd  in
                    match uu____22439 with
                    | (lb1,uu____22455,uu____22456) ->
                        let uu____22473 = lec2  in
                        (match uu____22473 with
                         | (lb2,uu____22489,uu____22490) ->
                             let msg =
                               let uu____22509 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____22511 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____22509 uu____22511
                                in
                             let uu____22514 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____22514))
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
                 let uu____22710 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____22710
                 then ()
                 else
                   (let uu____22715 = lec_hd  in
                    match uu____22715 with
                    | (lb1,uu____22731,uu____22732) ->
                        let uu____22749 = lec2  in
                        (match uu____22749 with
                         | (lb2,uu____22765,uu____22766) ->
                             let msg =
                               let uu____22785 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____22787 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____22785 uu____22787
                                in
                             let uu____22790 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____22790))
                  in
               let lecs1 =
                 let uu____22809 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____22910 = univs_and_uvars_of_lec this_lec  in
                        match uu____22910 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____22809 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____23137 = lec_hd  in
                   match uu____23137 with
                   | (lbname,e,c) ->
                       let uu____23171 =
                         let uu____23177 =
                           let uu____23179 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____23181 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____23183 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____23179 uu____23181 uu____23183
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____23177)
                          in
                       let uu____23187 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____23171 uu____23187
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____23240 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____23240 with
                         | FStar_Pervasives_Native.Some uu____23258 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____23279 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____23295 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____23295 with
                              | (bs,kres) ->
                                  ((let uu____23371 =
                                      let uu____23372 =
                                        let uu____23383 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____23383
                                         in
                                      uu____23372.FStar_Syntax_Syntax.n  in
                                    match uu____23371 with
                                    | FStar_Syntax_Syntax.Tm_type uu____23392
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____23401 =
                                          let uu____23403 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____23403  in
                                        if uu____23401
                                        then fail1 kres
                                        else ()
                                    | uu____23413 -> fail1 kres);
                                   (let a =
                                      let uu____23425 =
                                        let uu____23428 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _23431  ->
                                             FStar_Pervasives_Native.Some
                                               _23431) uu____23428
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____23425
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____23456 ->
                                          let uu____23470 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____23470
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
                      (fun uu____23675  ->
                         match uu____23675 with
                         | (lbname,e,c) ->
                             let uu____23792 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____23918 ->
                                   let uu____23938 = (e, c)  in
                                   (match uu____23938 with
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
                                                (fun uu____24056  ->
                                                   match uu____24056 with
                                                   | (x,uu____24067) ->
                                                       let uu____24078 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____24078)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____24122 =
                                                let uu____24124 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____24124
                                                 in
                                              if uu____24122
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
                                          let uu____24159 =
                                            let uu____24160 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____24160.FStar_Syntax_Syntax.n
                                             in
                                          match uu____24159 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____24215 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____24215 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____24247 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____24266 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____24266, gen_tvars))
                                in
                             (match uu____23792 with
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
        (let uu____24656 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____24656
         then
           let uu____24659 =
             let uu____24661 =
               FStar_List.map
                 (fun uu____24684  ->
                    match uu____24684 with
                    | (lb,uu____24701,uu____24702) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____24661 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____24659
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____24756  ->
                match uu____24756 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____24821 = gen env is_rec lecs  in
           match uu____24821 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____24986  ->
                       match uu____24986 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____25114 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____25114
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____25182  ->
                           match uu____25182 with
                           | (l,us,e,c,gvs) ->
                               let uu____25246 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____25248 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____25250 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____25252 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____25254 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____25246 uu____25248 uu____25250
                                 uu____25252 uu____25254))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____25321  ->
                match uu____25321 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____25407 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____25407, t, c, gvs)) univnames_lecs
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
              (let uu____25868 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____25868 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____25898 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _25921  -> FStar_Pervasives_Native.Some _25921)
                     uu____25898)
             in
          let is_var e1 =
            let uu____25937 =
              let uu____25938 = FStar_Syntax_Subst.compress e1  in
              uu____25938.FStar_Syntax_Syntax.n  in
            match uu____25937 with
            | FStar_Syntax_Syntax.Tm_name uu____25950 -> true
            | uu____25957 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1273_26015 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1273_26015.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1273_26015.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____26026 -> e2  in
          let env2 =
            let uu___1276_26136 = env1  in
            let uu____26245 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1276_26136.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1276_26136.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1276_26136.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1276_26136.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1276_26136.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1276_26136.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1276_26136.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1276_26136.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1276_26136.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1276_26136.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1276_26136.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1276_26136.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1276_26136.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1276_26136.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1276_26136.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1276_26136.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1276_26136.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____26245;
              FStar_TypeChecker_Env.is_iface =
                (uu___1276_26136.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1276_26136.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1276_26136.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1276_26136.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1276_26136.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1276_26136.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1276_26136.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1276_26136.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1276_26136.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1276_26136.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1276_26136.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1276_26136.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1276_26136.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1276_26136.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1276_26136.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1276_26136.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1276_26136.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1276_26136.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1276_26136.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1276_26136.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1276_26136.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1276_26136.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1276_26136.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1276_26136.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1276_26136.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____26247 = check1 env2 t1 t2  in
          match uu____26247 with
          | FStar_Pervasives_Native.None  ->
              let uu____26270 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____26276 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____26270 uu____26276
          | FStar_Pervasives_Native.Some g ->
              ((let uu____26299 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____26299
                then
                  let uu____26304 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____26304
                else ());
               (let uu____26310 = decorate e t2  in (uu____26310, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____26494 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____26494
         then
           let uu____26497 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____26497
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____26527 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____26527
         then
           let uu____26539 = discharge g1  in
           let uu____26541 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____26539, uu____26541)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____26580 =
                let uu____26589 =
                  let uu____26598 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____26598
                    FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____26589
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____26580
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____26676 = destruct_comp c1  in
            match uu____26676 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____26730 = FStar_TypeChecker_Env.get_range env  in
                  let uu____26731 =
                    let uu____26736 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____26745 =
                      let uu____26746 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____26759 =
                        let uu____26774 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____26774]  in
                      uu____26746 :: uu____26759  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____26736 uu____26745  in
                  uu____26731 FStar_Pervasives_Native.None uu____26730  in
                ((let uu____26824 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____26824
                  then
                    let uu____26829 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____26829
                  else ());
                 (let g2 =
                    let uu____26843 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____26843  in
                  let uu____26856 = discharge g2  in
                  let uu____26858 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____26856, uu____26858)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_26920 =
        match uu___8_26920 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____26934)::[] -> f fst1
        | uu____26975 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____26995 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____26995
          (fun _27008  -> FStar_TypeChecker_Common.NonTrivial _27008)
         in
      let op_or_e e =
        let uu____27027 =
          let uu____27036 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____27036  in
        FStar_All.pipe_right uu____27027
          (fun _27051  -> FStar_TypeChecker_Common.NonTrivial _27051)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _27070  -> FStar_TypeChecker_Common.NonTrivial _27070)
         in
      let op_or_t t =
        let uu____27089 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____27089
          (fun _27112  -> FStar_TypeChecker_Common.NonTrivial _27112)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _27131  -> FStar_TypeChecker_Common.NonTrivial _27131)
         in
      let short_op_ite uu___9_27137 =
        match uu___9_27137 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____27151)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____27194)::[] ->
            let uu____27259 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____27259
              (fun _27272  -> FStar_TypeChecker_Common.NonTrivial _27272)
        | uu____27273 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____27289 =
          let uu____27301 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____27301)  in
        let uu____27313 =
          let uu____27327 =
            let uu____27339 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____27339)  in
          let uu____27351 =
            let uu____27365 =
              let uu____27377 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____27377)  in
            let uu____27389 =
              let uu____27403 =
                let uu____27415 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____27415)  in
              let uu____27427 =
                let uu____27441 =
                  let uu____27453 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____27453)  in
                [uu____27441; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____27403 :: uu____27427  in
            uu____27365 :: uu____27389  in
          uu____27327 :: uu____27351  in
        uu____27289 :: uu____27313  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____27566 =
            FStar_Util.find_map table
              (fun uu____27585  ->
                 match uu____27585 with
                 | (x,mk1) ->
                     let uu____27614 = FStar_Ident.lid_equals x lid  in
                     if uu____27614
                     then
                       let uu____27619 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____27619
                     else FStar_Pervasives_Native.None)
             in
          (match uu____27566 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____27623 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____27639 =
      let uu____27640 = FStar_Syntax_Util.un_uinst l  in
      uu____27640.FStar_Syntax_Syntax.n  in
    match uu____27639 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____27688 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____27842)::uu____27843 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____27882 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____27896,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____27897))::uu____27898 -> bs
      | uu____27936 ->
          let uu____27937 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____27937 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____27957 =
                 let uu____27958 = FStar_Syntax_Subst.compress t  in
                 uu____27958.FStar_Syntax_Syntax.n  in
               (match uu____27957 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____27970) ->
                    let uu____28009 =
                      FStar_Util.prefix_until
                        (fun uu___10_28069  ->
                           match uu___10_28069 with
                           | (uu____28082,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____28083)) ->
                               false
                           | uu____28098 -> true) bs'
                       in
                    (match uu____28009 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____28154,uu____28155) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____28272,uu____28273) ->
                         let uu____28391 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____28421  ->
                                   match uu____28421 with
                                   | (x,uu____28435) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____28391
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____28519  ->
                                     match uu____28519 with
                                     | (x,i) ->
                                         let uu____28558 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____28558, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____28589 -> bs))
  
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
            let uu____28778 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____28778
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
          let uu____28973 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____28973
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
        (let uu____29174 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____29174
         then
           ((let uu____29179 = FStar_Ident.text_of_lid lident  in
             d uu____29179);
            (let uu____29181 = FStar_Ident.text_of_lid lident  in
             let uu____29183 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____29181 uu____29183))
         else ());
        (let fv =
           let uu____29195 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____29195
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
         let uu____29264 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1434_29283 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1434_29283.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1434_29283.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1434_29283.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1434_29283.FStar_Syntax_Syntax.sigattrs)
           }), uu____29264))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_29429 =
        match uu___11_29429 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____29432 -> false  in
      let reducibility uu___12_29440 =
        match uu___12_29440 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____29447 -> false  in
      let assumption uu___13_29455 =
        match uu___13_29455 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____29459 -> false  in
      let reification uu___14_29467 =
        match uu___14_29467 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____29470 -> true
        | uu____29476 -> false  in
      let inferred uu___15_29484 =
        match uu___15_29484 with
        | FStar_Syntax_Syntax.Discriminator uu____29486 -> true
        | FStar_Syntax_Syntax.Projector uu____29492 -> true
        | FStar_Syntax_Syntax.RecordType uu____29504 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____29518 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____29535 -> false  in
      let has_eq uu___16_29543 =
        match uu___16_29543 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____29547 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____29626 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____29637 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____29648 =
        let uu____29650 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_29656  ->
                  match uu___17_29656 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____29659 -> false))
           in
        FStar_All.pipe_right uu____29650 Prims.op_Negation  in
      if uu____29648
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____29680 =
            let uu____29686 =
              let uu____29688 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____29688 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____29686)  in
          FStar_Errors.raise_error uu____29680 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____29706 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____29714 =
            let uu____29716 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____29716  in
          if uu____29714 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____29726),uu____29727) ->
              ((let uu____29761 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____29761
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____29770 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____29770
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____29781 ->
              let uu____29799 =
                let uu____29801 =
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
                Prims.op_Negation uu____29801  in
              if uu____29799 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____29811 ->
              let uu____29826 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____29826 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____29834 ->
              let uu____29849 =
                let uu____29851 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____29851  in
              if uu____29849 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____29861 ->
              let uu____29882 =
                let uu____29884 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____29884  in
              if uu____29882 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____29894 ->
              let uu____29915 =
                let uu____29917 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____29917  in
              if uu____29915 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____29927 ->
              let uu____29948 =
                let uu____29950 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____29950  in
              if uu____29948 then err'1 () else ()
          | uu____29960 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____30105 =
          let uu____30114 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____30114
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____30105
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____30168 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____30168
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____30214 =
                          let uu____30215 = FStar_Syntax_Subst.compress t1
                             in
                          uu____30215.FStar_Syntax_Syntax.n  in
                        match uu____30214 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____30236 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____30436 =
          let uu____30437 = FStar_Syntax_Subst.compress t1  in
          uu____30437.FStar_Syntax_Syntax.n  in
        match uu____30436 with
        | FStar_Syntax_Syntax.Tm_type uu____30449 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____30455 ->
            let uu____30479 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____30479 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____30647 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____30647
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____30653;
               FStar_Syntax_Syntax.index = uu____30654;
               FStar_Syntax_Syntax.sort = t2;_},uu____30656)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____30684,uu____30685) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____30767::[]) ->
            let uu____30830 =
              let uu____30831 = FStar_Syntax_Util.un_uinst head1  in
              uu____30831.FStar_Syntax_Syntax.n  in
            (match uu____30830 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____30847 -> false)
        | uu____30849 -> false
      
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
        (let uu____30925 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____30925
         then
           let uu____30930 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____30930
         else ());
        res
       in aux g t
  