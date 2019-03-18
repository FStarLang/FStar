open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____60630 = FStar_TypeChecker_Env.get_range env  in
      let uu____60631 =
        FStar_TypeChecker_Err.failed_to_prove_specification errs  in
      FStar_Errors.log_issue uu____60630 uu____60631
  
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
        let uu____60692 =
          let uu____60694 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____60694  in
        if uu____60692
        then g
        else
          (let uu____60701 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____60753  ->
                     match uu____60753 with
                     | (uu____60760,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____60701 with
           | (solve_now,defer) ->
               ((let uu____60795 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____60795
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____60812  ->
                         match uu____60812 with
                         | (s,p) ->
                             let uu____60822 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____60822)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____60837  ->
                         match uu____60837 with
                         | (s,p) ->
                             let uu____60847 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____60847)
                      defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___631_60855 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___631_60855.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___631_60855.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___631_60855.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___634_60857 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___634_60857.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___634_60857.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___634_60857.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____60872 =
        let uu____60874 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____60874  in
      if uu____60872
      then
        let us =
          let uu____60879 =
            let uu____60883 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____60883
             in
          FStar_All.pipe_right uu____60879 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____60902 =
            let uu____60908 =
              let uu____60910 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____60910
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____60908)  in
          FStar_Errors.log_issue r uu____60902);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____60933  ->
      match uu____60933 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____60944;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____60946;
          FStar_Syntax_Syntax.lbpos = uu____60947;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____60982 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 e  in
               (match uu____60982 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____61020) ->
                          aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____61027)
                          -> FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____61082) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____61118 = FStar_Options.ml_ish ()  in
                                if uu____61118
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____61140 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____61140
                            then
                              let uu____61143 = FStar_Range.string_of_range r
                                 in
                              let uu____61145 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____61143 uu____61145
                            else ());
                           FStar_Util.Inl t2)
                      | uu____61150 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____61152 = aux e1  in
                      match uu____61152 with
                      | FStar_Util.Inr c ->
                          let uu____61158 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____61158
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____61163 =
                               let uu____61169 =
                                 let uu____61171 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____61171
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____61169)
                                in
                             FStar_Errors.raise_error uu____61163 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____61180 ->
               let uu____61181 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____61181 with
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
    let pat_as_arg uu____61245 =
      match uu____61245 with
      | (p,i) ->
          let uu____61265 = decorated_pattern_as_term p  in
          (match uu____61265 with
           | (vars,te) ->
               let uu____61288 =
                 let uu____61293 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____61293)  in
               (vars, uu____61288))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____61307 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____61307)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____61311 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____61311)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____61315 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____61315)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____61338 =
          let uu____61357 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____61357 FStar_List.unzip  in
        (match uu____61338 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____61495 =
               let uu____61496 =
                 let uu____61497 =
                   let uu____61514 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____61514, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____61497  in
               mk1 uu____61496  in
             (vars1, uu____61495))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____61553,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____61563,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____61577 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____61588 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp
       in
    FStar_All.pipe_right uu____61588 comp_univ_opt
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____61617)::[] -> wp
      | uu____61642 ->
          let uu____61653 =
            let uu____61655 =
              let uu____61657 =
                FStar_List.map
                  (fun uu____61671  ->
                     match uu____61671 with
                     | (x,uu____61680) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____61657 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____61655
             in
          failwith uu____61653
       in
    let uu____61691 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____61691, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____61708 = destruct_comp c  in
        match uu____61708 with
        | (u,uu____61716,wp) ->
            let uu____61718 =
              let uu____61729 =
                let uu____61738 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____61738  in
              [uu____61729]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____61718;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____61771 =
          let uu____61778 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____61779 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____61778 uu____61779  in
        match uu____61771 with | (m,uu____61781,uu____61782) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____61799 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____61799
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
        let uu____61846 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____61846 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____61883 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____61883 with
             | (a,kwp) ->
                 let uu____61914 = destruct_comp m1  in
                 let uu____61921 = destruct_comp m2  in
                 ((md, a, kwp), uu____61914, uu____61921))
  
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
            let uu____62006 =
              let uu____62007 =
                let uu____62018 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____62018]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____62007;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____62006
  
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
          let uu____62102 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____62102
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
      let uu____62118 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        uu____62118 lc.FStar_Syntax_Syntax.cflags
        (fun uu____62121  ->
           let uu____62122 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____62122)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____62130 =
      let uu____62131 = FStar_Syntax_Subst.compress t  in
      uu____62131.FStar_Syntax_Syntax.n  in
    match uu____62130 with
    | FStar_Syntax_Syntax.Tm_arrow uu____62135 -> true
    | uu____62151 -> false
  
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
              let uu____62221 =
                let uu____62223 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____62223  in
              if uu____62221
              then f
              else (let uu____62230 = reason1 ()  in label uu____62230 r f)
  
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
            let uu___828_62251 = g  in
            let uu____62252 =
              let uu____62253 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____62253  in
            {
              FStar_TypeChecker_Env.guard_f = uu____62252;
              FStar_TypeChecker_Env.deferred =
                (uu___828_62251.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___828_62251.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___828_62251.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____62274 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____62274
        then c
        else
          (let uu____62279 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____62279
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____62341 = FStar_Syntax_Syntax.mk_binder x
                            in
                         [uu____62341]  in
                       let us =
                         let uu____62363 =
                           let uu____62366 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____62366]  in
                         u_res :: uu____62363  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____62372 =
                         let uu____62377 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____62378 =
                           let uu____62379 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____62388 =
                             let uu____62399 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____62408 =
                               let uu____62419 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____62419]  in
                             uu____62399 :: uu____62408  in
                           uu____62379 :: uu____62388  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____62377
                           uu____62378
                          in
                       uu____62372 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____62461 = destruct_comp c1  in
              match uu____62461 with
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
          (fun uu____62497  ->
             let uu____62498 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____62498)
  
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
              ({ FStar_Syntax_Syntax.ppname = uu____62521;
                 FStar_Syntax_Syntax.index = uu____62522;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____62524;
                     FStar_Syntax_Syntax.vars = uu____62525;_};_},uu____62526)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____62534 -> c
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___585_62546  ->
            match uu___585_62546 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____62549 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit =
          let uu____62574 =
            let uu____62577 =
              FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____62577 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____62574
            (fun c  ->
               (let uu____62633 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____62633) &&
                 (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                    FStar_Syntax_Util.is_unit))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit))
               &&
               (let uu____62645 = FStar_Syntax_Util.head_and_args' e  in
                match uu____62645 with
                | (head1,uu____62662) ->
                    let uu____62683 =
                      let uu____62684 = FStar_Syntax_Util.un_uinst head1  in
                      uu____62684.FStar_Syntax_Syntax.n  in
                    (match uu____62683 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____62689 =
                           let uu____62691 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____62691
                            in
                         Prims.op_Negation uu____62689
                     | uu____62692 -> true)))
              &&
              (let uu____62695 = should_not_inline_lc lc  in
               Prims.op_Negation uu____62695)
  
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
            let uu____62723 =
              let uu____62725 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____62725  in
            if uu____62723
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____62732 = FStar_Syntax_Util.is_unit t  in
               if uu____62732
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
                    let uu____62741 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____62741
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____62746 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____62746 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____62756 =
                             let uu____62757 =
                               let uu____62762 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____62763 =
                                 let uu____62764 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____62773 =
                                   let uu____62784 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____62784]  in
                                 uu____62764 :: uu____62773  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____62762
                                 uu____62763
                                in
                             uu____62757 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env
                             uu____62756)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____62818 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____62818
           then
             let uu____62823 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____62825 = FStar_Syntax_Print.term_to_string v1  in
             let uu____62827 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____62823 uu____62825 uu____62827
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____62844 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___586_62850  ->
              match uu___586_62850 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____62853 -> false))
       in
    if uu____62844
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___587_62865  ->
              match uu___587_62865 with
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
        let uu____62885 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____62885
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____62891 = destruct_comp c1  in
           match uu____62891 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____62905 =
                   let uu____62910 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____62911 =
                     let uu____62912 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____62921 =
                       let uu____62932 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____62941 =
                         let uu____62952 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____62952]  in
                       uu____62932 :: uu____62941  in
                     uu____62912 :: uu____62921  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____62910 uu____62911  in
                 uu____62905 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____62993 = weaken_flags c1.FStar_Syntax_Syntax.flags
                  in
               mk_comp md u_res_t res_t wp1 uu____62993)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____63017 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____63019 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____63019
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____63025 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____63025 weaken
  
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
               let uu____63073 = destruct_comp c1  in
               match uu____63073 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____63087 =
                       let uu____63092 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____63093 =
                         let uu____63094 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____63103 =
                           let uu____63114 =
                             let uu____63123 =
                               let uu____63124 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____63124 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____63123
                              in
                           let uu____63133 =
                             let uu____63144 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____63144]  in
                           uu____63114 :: uu____63133  in
                         uu____63094 :: uu____63103  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____63092 uu____63093
                        in
                     uu____63087 FStar_Pervasives_Native.None
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
            let uu____63230 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____63230
            then (lc, g0)
            else
              (let flags =
                 let uu____63242 =
                   let uu____63250 =
                     FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
                   if uu____63250
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____63242 with
                 | (maybe_trivial_post,flags) ->
                     let uu____63280 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___588_63288  ->
                               match uu___588_63288 with
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
                               | uu____63291 -> []))
                        in
                     FStar_List.append flags uu____63280
                  in
               let strengthen uu____63297 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____63303 = FStar_TypeChecker_Env.guard_form g01
                       in
                    match uu____63303 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____63306 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____63306
                          then
                            let uu____63310 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____63312 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____63310 uu____63312
                          else ());
                         strengthen_comp env reason c f flags))
                  in
               let uu____63317 =
                 let uu____63318 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____63318
                   lc.FStar_Syntax_Syntax.res_typ flags strengthen
                  in
               (uu____63317,
                 (let uu___983_63320 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___983_63320.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___983_63320.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___983_63320.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___589_63329  ->
            match uu___589_63329 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____63333 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____63362 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____63362
          then e
          else
            (let uu____63369 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____63372 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____63372)
                in
             if uu____63369
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
          fun uu____63425  ->
            match uu____63425 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____63445 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____63445 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____63458 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____63458
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____63468 =
                         FStar_Syntax_Util.is_total_lcomp lc11  in
                       if uu____63468
                       then
                         let uu____63473 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____63473
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____63480 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____63480
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____63489 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____63489
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____63496 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____63496
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____63508 =
                  let uu____63509 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____63509
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
                       (fun uu____63526  ->
                          let uu____63527 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____63529 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____63534 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____63527 uu____63529 uu____63534);
                     (let aux uu____63552 =
                        let uu____63553 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____63553
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____63584 ->
                              let uu____63585 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____63585
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____63617 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____63617
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____63662 =
                        let uu____63663 =
                          let uu____63665 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____63665  in
                        if uu____63663
                        then
                          let uu____63679 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____63679
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____63702 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____63702))
                        else
                          (let uu____63717 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____63717
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___1049_63759 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1049_63759.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1049_63759.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____63760 =
                                 let uu____63766 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____63766, reason)  in
                               FStar_Util.Inl uu____63760  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____63802 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____63802
                                   (close1 x "c1 Tot")
                             | (uu____63816,FStar_Pervasives_Native.Some x)
                                 ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____63839,uu____63840) -> aux ()
                           else
                             (let uu____63855 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____63855
                              then
                                let uu____63868 =
                                  let uu____63874 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____63874, "both GTot")  in
                                FStar_Util.Inl uu____63868
                              else aux ()))
                         in
                      let uu____63885 = try_simplify ()  in
                      match uu____63885 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____63911  ->
                                let uu____63912 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____63912);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____63926  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____63948 = lift_and_destruct env c11 c21
                                 in
                              match uu____63948 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____64001 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____64001]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____64021 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____64021]
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
                                    let uu____64068 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____64077 =
                                      let uu____64088 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____64097 =
                                        let uu____64108 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____64117 =
                                          let uu____64128 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____64137 =
                                            let uu____64148 =
                                              let uu____64157 = mk_lam wp2
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____64157
                                               in
                                            [uu____64148]  in
                                          uu____64128 :: uu____64137  in
                                        uu____64108 :: uu____64117  in
                                      uu____64088 :: uu____64097  in
                                    uu____64068 :: uu____64077  in
                                  let wp =
                                    let uu____64209 =
                                      let uu____64214 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____64214 wp_args
                                       in
                                    uu____64209 FStar_Pervasives_Native.None
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
                              let uu____64237 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____64237 with
                              | (m,uu____64245,lift2) ->
                                  let c23 =
                                    let uu____64248 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____64248
                                     in
                                  let uu____64249 = destruct_comp c12  in
                                  (match uu____64249 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____64263 =
                                           let uu____64268 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____64269 =
                                             let uu____64270 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____64279 =
                                               let uu____64290 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____64290]  in
                                             uu____64270 :: uu____64279  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64268 uu____64269
                                            in
                                         uu____64263
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
                            let uu____64328 = destruct_comp c1_typ  in
                            match uu____64328 with
                            | (u_res_t1,res_t1,uu____64337) ->
                                let uu____64338 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____64338
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____64343 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____64343
                                   then
                                     (debug1
                                        (fun uu____64353  ->
                                           let uu____64354 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____64356 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____64354 uu____64356);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____64364 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____64367 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____64367)
                                         in
                                      if uu____64364
                                      then
                                        let e1' =
                                          let uu____64388 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____64388
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____64400  ->
                                              let uu____64401 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____64403 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____64401 uu____64403);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____64418  ->
                                              let uu____64419 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____64421 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____64419 uu____64421);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____64428 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____64428
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
      | uu____64446 -> g2
  
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
            (let uu____64470 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____64470)
           in
        let flags =
          if should_return1
          then
            let uu____64478 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____64478
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____64494 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____64498 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____64498
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____64504 =
              let uu____64506 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____64506  in
            (if uu____64504
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___1168_64513 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___1168_64513.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___1168_64513.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___1168_64513.FStar_Syntax_Syntax.effect_args);
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
               let uu____64526 =
                 let uu____64527 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____64527
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                 uu____64526
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____64530 =
               let uu____64531 =
                 let uu____64532 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____64532
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____64531  in
             FStar_Syntax_Util.comp_set_flags uu____64530 flags)
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
            fun uu____64570  ->
              match uu____64570 with
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
                    let uu____64582 =
                      ((let uu____64586 = is_pure_or_ghost_effect env eff1
                           in
                        Prims.op_Negation uu____64586) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____64582
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____64604 =
        let uu____64605 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____64605  in
      FStar_Syntax_Syntax.fvar uu____64604 FStar_Syntax_Syntax.delta_constant
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
               fun uu____64675  ->
                 match uu____64675 with
                 | (uu____64689,eff_label,uu____64691,uu____64692) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____64705 =
          let uu____64713 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____64751  ->
                    match uu____64751 with
                    | (uu____64766,uu____64767,flags,uu____64769) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___590_64786  ->
                                match uu___590_64786 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____64789 -> false))))
             in
          if uu____64713
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____64705 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____64822 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____64824 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____64824
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____64865 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____64866 =
                     let uu____64871 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____64872 =
                       let uu____64873 = FStar_Syntax_Syntax.as_arg res_t1
                          in
                       let uu____64882 =
                         let uu____64893 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____64902 =
                           let uu____64913 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____64922 =
                             let uu____64933 =
                               FStar_Syntax_Syntax.as_arg wp_e  in
                             [uu____64933]  in
                           uu____64913 :: uu____64922  in
                         uu____64893 :: uu____64902  in
                       uu____64873 :: uu____64882  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____64871 uu____64872
                      in
                   uu____64866 FStar_Pervasives_Native.None uu____64865  in
                 let default_case =
                   let post_k =
                     let uu____64986 =
                       let uu____64995 =
                         FStar_Syntax_Syntax.null_binder res_t  in
                       [uu____64995]  in
                     let uu____65014 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____64986 uu____65014  in
                   let kwp =
                     let uu____65020 =
                       let uu____65029 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____65029]  in
                     let uu____65048 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____65020 uu____65048  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____65055 =
                       let uu____65056 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____65056]  in
                     let uu____65075 =
                       let uu____65078 =
                         let uu____65085 =
                           FStar_TypeChecker_Env.get_range env  in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____65085
                          in
                       let uu____65086 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____65078 uu____65086  in
                     FStar_Syntax_Util.abs uu____65055 uu____65075
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
                   let uu____65110 =
                     should_not_inline_whole_match ||
                       (let uu____65113 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____65113)
                      in
                   if uu____65110 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____65152  ->
                        fun celse  ->
                          match uu____65152 with
                          | (g,eff_label,uu____65169,cthen) ->
                              let uu____65183 =
                                let uu____65208 =
                                  let uu____65209 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____65209
                                   in
                                lift_and_destruct env uu____65208 celse  in
                              (match uu____65183 with
                               | ((md,uu____65211,uu____65212),(uu____65213,uu____65214,wp_then),
                                  (uu____65216,uu____65217,wp_else)) ->
                                   let uu____65237 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____65237 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____65252::[] -> comp
                 | uu____65295 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____65314 = destruct_comp comp1  in
                     (match uu____65314 with
                      | (uu____65321,uu____65322,wp) ->
                          let wp1 =
                            let uu____65327 =
                              let uu____65332 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____65333 =
                                let uu____65334 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____65343 =
                                  let uu____65354 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____65354]  in
                                uu____65334 :: uu____65343  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____65332
                                uu____65333
                               in
                            uu____65327 FStar_Pervasives_Native.None
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
          let uu____65420 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____65420 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____65436 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____65442 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____65436 uu____65442
              else
                (let uu____65451 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____65457 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____65451 uu____65457)
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
          let uu____65482 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____65482
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____65485 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____65485
        then u_res
        else
          (let is_total =
             let uu____65492 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____65492
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____65503 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____65503 with
              | FStar_Pervasives_Native.None  ->
                  let uu____65506 =
                    let uu____65512 =
                      let uu____65514 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____65514
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____65512)
                     in
                  FStar_Errors.raise_error uu____65506
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
               let uu____65559 =
                 let uu____65560 = FStar_Syntax_Subst.compress t2  in
                 uu____65560.FStar_Syntax_Syntax.n  in
               match uu____65559 with
               | FStar_Syntax_Syntax.Tm_type uu____65564 -> true
               | uu____65566 -> false  in
             let uu____65568 =
               let uu____65569 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____65569.FStar_Syntax_Syntax.n  in
             match uu____65568 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____65577 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____65587 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____65587
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____65590 =
                     let uu____65591 =
                       let uu____65592 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____65592
                        in
                     (FStar_Pervasives_Native.None, uu____65591)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____65590
                    in
                 let e1 =
                   let uu____65598 =
                     let uu____65603 =
                       let uu____65604 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____65604]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____65603  in
                   uu____65598 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____65629 -> (e, lc))
  
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
          (let uu____65664 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____65664
           then
             let uu____65667 = FStar_Syntax_Print.term_to_string e  in
             let uu____65669 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____65671 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____65667 uu____65669 uu____65671
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____65681 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____65681 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____65706 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____65732 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____65732, false)
             else
               (let uu____65742 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____65742, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____65755) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____65767 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____65767
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___1324_65783 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___1324_65783.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___1324_65783.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___1324_65783.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____65790 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____65790 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____65802 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t  in
                      let uu____65813 =
                        let uu____65815 = FStar_Syntax_Util.eq_tm t res_t  in
                        uu____65815 = FStar_Syntax_Util.Equal  in
                      if uu____65813
                      then
                        ((let uu____65818 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____65818
                          then
                            let uu____65822 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____65824 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____65822 uu____65824
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
                           | FStar_Syntax_Syntax.Tm_refine uu____65835 ->
                               true
                           | uu____65843 -> false  in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t
                              in
                           let cret =
                             let uu____65848 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             return_value env (comp_univ_opt c) res_t
                               uu____65848
                              in
                           let lc1 =
                             let uu____65850 =
                               FStar_Syntax_Util.lcomp_of_comp c  in
                             let uu____65851 =
                               let uu____65852 =
                                 FStar_Syntax_Util.lcomp_of_comp cret  in
                               ((FStar_Pervasives_Native.Some x),
                                 uu____65852)
                                in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____65850
                               uu____65851
                              in
                           ((let uu____65856 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____65856
                             then
                               let uu____65860 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____65862 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               let uu____65864 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____65866 =
                                 FStar_Syntax_Print.lcomp_to_string lc1  in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____65860 uu____65862 uu____65864
                                 uu____65866
                             else ());
                            (let uu____65871 =
                               FStar_Syntax_Syntax.lcomp_comp lc1  in
                             set_result_typ1 uu____65871))
                         else
                           ((let uu____65875 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____65875
                             then
                               let uu____65879 =
                                 FStar_Syntax_Print.term_to_string res_t  in
                               let uu____65881 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____65879 uu____65881
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
                      let uu___1356_65889 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1356_65889.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1356_65889.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1356_65889.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____65895 =
                      let uu____65896 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____65896
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____65902 =
                           let uu____65903 = FStar_Syntax_Subst.compress f1
                              in
                           uu____65903.FStar_Syntax_Syntax.n  in
                         match uu____65902 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____65906,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____65908;
                                            FStar_Syntax_Syntax.vars =
                                              uu____65909;_},uu____65910)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1372_65936 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___1372_65936.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___1372_65936.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___1372_65936.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____65937 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____65940 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____65940
                               then
                                 let uu____65944 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____65946 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____65948 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____65950 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____65944 uu____65946 uu____65948
                                   uu____65950
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
                                   let uu____65963 =
                                     let uu____65968 =
                                       let uu____65969 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____65969]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____65968
                                      in
                                   uu____65963 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____65996 =
                                 let uu____66001 =
                                   FStar_All.pipe_left
                                     (fun _66022  ->
                                        FStar_Pervasives_Native.Some _66022)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____66023 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____66024 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____66025 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____66001
                                   uu____66023 e uu____66024 uu____66025
                                  in
                               match uu____65996 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___1388_66029 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___1388_66029.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___1388_66029.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____66031 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____66031
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____66036 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____66036
                                     then
                                       let uu____66040 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____66040
                                     else ());
                                    c2))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___591_66053  ->
                              match uu___591_66053 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____66056 -> []))
                       in
                    let lc1 =
                      let uu____66058 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____66058 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1402_66060 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1402_66060.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1402_66060.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1402_66060.FStar_TypeChecker_Env.implicits)
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
        let uu____66096 =
          let uu____66099 =
            let uu____66104 =
              let uu____66105 =
                let uu____66114 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____66114  in
              [uu____66105]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____66104  in
          uu____66099 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____66096  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____66137 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____66137
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____66156 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____66172 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____66189 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____66189
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____66205)::(ens,uu____66207)::uu____66208 ->
                    let uu____66251 =
                      let uu____66254 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____66254  in
                    let uu____66255 =
                      let uu____66256 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____66256  in
                    (uu____66251, uu____66255)
                | uu____66259 ->
                    let uu____66270 =
                      let uu____66276 =
                        let uu____66278 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____66278
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____66276)
                       in
                    FStar_Errors.raise_error uu____66270
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____66298)::uu____66299 ->
                    let uu____66326 =
                      let uu____66331 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____66331
                       in
                    (match uu____66326 with
                     | (us_r,uu____66363) ->
                         let uu____66364 =
                           let uu____66369 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____66369
                            in
                         (match uu____66364 with
                          | (us_e,uu____66401) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____66404 =
                                  let uu____66405 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____66405
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____66404
                                  us_r
                                 in
                              let as_ens =
                                let uu____66407 =
                                  let uu____66408 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____66408
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____66407
                                  us_e
                                 in
                              let req =
                                let uu____66412 =
                                  let uu____66417 =
                                    let uu____66418 =
                                      let uu____66429 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____66429]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____66418
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____66417
                                   in
                                uu____66412 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____66469 =
                                  let uu____66474 =
                                    let uu____66475 =
                                      let uu____66486 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____66486]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____66475
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____66474
                                   in
                                uu____66469 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____66523 =
                                let uu____66526 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____66526  in
                              let uu____66527 =
                                let uu____66528 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____66528  in
                              (uu____66523, uu____66527)))
                | uu____66531 -> failwith "Impossible"))
  
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
      (let uu____66565 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____66565
       then
         let uu____66570 = FStar_Syntax_Print.term_to_string tm  in
         let uu____66572 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____66570
           uu____66572
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
        (let uu____66626 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____66626
         then
           let uu____66631 = FStar_Syntax_Print.term_to_string tm  in
           let uu____66633 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____66631
             uu____66633
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____66644 =
      let uu____66646 =
        let uu____66647 = FStar_Syntax_Subst.compress t  in
        uu____66647.FStar_Syntax_Syntax.n  in
      match uu____66646 with
      | FStar_Syntax_Syntax.Tm_app uu____66651 -> false
      | uu____66669 -> true  in
    if uu____66644
    then t
    else
      (let uu____66674 = FStar_Syntax_Util.head_and_args t  in
       match uu____66674 with
       | (head1,args) ->
           let uu____66717 =
             let uu____66719 =
               let uu____66720 = FStar_Syntax_Subst.compress head1  in
               uu____66720.FStar_Syntax_Syntax.n  in
             match uu____66719 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____66725 -> false  in
           if uu____66717
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____66757 ->
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
          ((let uu____66804 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____66804
            then
              let uu____66807 = FStar_Syntax_Print.term_to_string e  in
              let uu____66809 = FStar_Syntax_Print.term_to_string t  in
              let uu____66811 =
                let uu____66813 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____66813
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____66807 uu____66809 uu____66811
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____66826 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____66826 with
              | (formals,uu____66842) ->
                  let n_implicits =
                    let uu____66864 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____66942  ->
                              match uu____66942 with
                              | (uu____66950,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____66957 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____66957 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____66864 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____67082 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____67082 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____67096 =
                      let uu____67102 =
                        let uu____67104 = FStar_Util.string_of_int n_expected
                           in
                        let uu____67106 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____67108 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____67104 uu____67106 uu____67108
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____67102)
                       in
                    let uu____67112 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____67096 uu____67112
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___592_67130 =
              match uu___592_67130 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____67173 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____67173 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _67304,uu____67291)
                           when _67304 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____67337,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____67339))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____67373 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____67373 with
                            | (v1,uu____67414,g) ->
                                ((let uu____67429 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____67429
                                  then
                                    let uu____67432 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____67432
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____67442 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____67442 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____67535 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____67535))))
                       | (uu____67562,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____67599 =
                             let uu____67612 =
                               let uu____67619 =
                                 let uu____67624 = FStar_Dyn.mkdyn env  in
                                 (uu____67624, tau)  in
                               FStar_Pervasives_Native.Some uu____67619  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____67612
                              in
                           (match uu____67599 with
                            | (v1,uu____67657,g) ->
                                ((let uu____67672 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____67672
                                  then
                                    let uu____67675 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____67675
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____67685 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____67685 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____67778 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____67778))))
                       | (uu____67805,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____67853 =
                       let uu____67880 = inst_n_binders t1  in
                       aux [] uu____67880 bs1  in
                     (match uu____67853 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____67952) -> (e, torig, guard)
                           | (uu____67983,[]) when
                               let uu____68014 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____68014 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____68016 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____68044 ->
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
            | uu____68057 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____68069 =
      let uu____68073 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____68073
        (FStar_List.map
           (fun u  ->
              let uu____68085 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____68085 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____68069 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____68113 = FStar_Util.set_is_empty x  in
      if uu____68113
      then []
      else
        (let s =
           let uu____68131 =
             let uu____68134 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____68134  in
           FStar_All.pipe_right uu____68131 FStar_Util.set_elements  in
         (let uu____68150 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____68150
          then
            let uu____68155 =
              let uu____68157 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____68157  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____68155
          else ());
         (let r =
            let uu____68166 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____68166  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____68205 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____68205
                     then
                       let uu____68210 =
                         let uu____68212 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____68212
                          in
                       let uu____68216 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____68218 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____68210 uu____68216 uu____68218
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
        let uu____68248 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____68248 FStar_Util.set_elements  in
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
        | ([],uu____68287) -> generalized_univ_names
        | (uu____68294,[]) -> explicit_univ_names
        | uu____68301 ->
            let uu____68310 =
              let uu____68316 =
                let uu____68318 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____68318
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____68316)
               in
            FStar_Errors.raise_error uu____68310 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____68340 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____68340
       then
         let uu____68345 = FStar_Syntax_Print.term_to_string t  in
         let uu____68347 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____68345 uu____68347
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____68356 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____68356
        then
          let uu____68361 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____68361
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____68370 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____68370
         then
           let uu____68375 = FStar_Syntax_Print.term_to_string t  in
           let uu____68377 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____68375 uu____68377
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
        let uu____68461 =
          let uu____68463 =
            FStar_Util.for_all
              (fun uu____68477  ->
                 match uu____68477 with
                 | (uu____68487,uu____68488,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____68463  in
        if uu____68461
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____68540 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____68540
              then
                let uu____68543 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____68543
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____68550 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____68550
               then
                 let uu____68553 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____68553
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____68571 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____68571 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____68605 =
             match uu____68605 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____68642 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____68642
                   then
                     let uu____68647 =
                       let uu____68649 =
                         let uu____68653 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____68653
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____68649
                         (FStar_String.concat ", ")
                        in
                     let uu____68701 =
                       let uu____68703 =
                         let uu____68707 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____68707
                           (FStar_List.map
                              (fun u  ->
                                 let uu____68720 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____68722 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____68720
                                   uu____68722))
                          in
                       FStar_All.pipe_right uu____68703
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____68647
                       uu____68701
                   else ());
                  (let univs2 =
                     let uu____68736 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____68748 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____68748) univs1
                       uu____68736
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____68755 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____68755
                    then
                      let uu____68760 =
                        let uu____68762 =
                          let uu____68766 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____68766
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____68762
                          (FStar_String.concat ", ")
                         in
                      let uu____68814 =
                        let uu____68816 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____68830 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____68832 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____68830
                                    uu____68832))
                           in
                        FStar_All.pipe_right uu____68816
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____68760 uu____68814
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____68853 =
             let uu____68870 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____68870  in
           match uu____68853 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____68960 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____68960
                 then ()
                 else
                   (let uu____68965 = lec_hd  in
                    match uu____68965 with
                    | (lb1,uu____68973,uu____68974) ->
                        let uu____68975 = lec2  in
                        (match uu____68975 with
                         | (lb2,uu____68983,uu____68984) ->
                             let msg =
                               let uu____68987 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____68989 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____68987 uu____68989
                                in
                             let uu____68992 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____68992))
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
                 let uu____69060 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____69060
                 then ()
                 else
                   (let uu____69065 = lec_hd  in
                    match uu____69065 with
                    | (lb1,uu____69073,uu____69074) ->
                        let uu____69075 = lec2  in
                        (match uu____69075 with
                         | (lb2,uu____69083,uu____69084) ->
                             let msg =
                               let uu____69087 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____69089 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____69087 uu____69089
                                in
                             let uu____69092 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____69092))
                  in
               let lecs1 =
                 let uu____69103 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____69156 = univs_and_uvars_of_lec this_lec  in
                        match uu____69156 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____69103 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____69261 = lec_hd  in
                   match uu____69261 with
                   | (lbname,e,c) ->
                       let uu____69271 =
                         let uu____69277 =
                           let uu____69279 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____69281 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____69283 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____69279 uu____69281 uu____69283
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____69277)
                          in
                       let uu____69287 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____69271 uu____69287
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____69306 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____69306 with
                         | FStar_Pervasives_Native.Some uu____69315 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____69323 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____69327 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____69327 with
                              | (bs,kres) ->
                                  ((let uu____69371 =
                                      let uu____69372 =
                                        let uu____69375 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____69375
                                         in
                                      uu____69372.FStar_Syntax_Syntax.n  in
                                    match uu____69371 with
                                    | FStar_Syntax_Syntax.Tm_type uu____69376
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____69380 =
                                          let uu____69382 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____69382  in
                                        if uu____69380
                                        then fail1 kres
                                        else ()
                                    | uu____69387 -> fail1 kres);
                                   (let a =
                                      let uu____69389 =
                                        let uu____69392 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _69395  ->
                                             FStar_Pervasives_Native.Some
                                               _69395) uu____69392
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____69389
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____69403 ->
                                          let uu____69412 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____69412
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
                      (fun uu____69515  ->
                         match uu____69515 with
                         | (lbname,e,c) ->
                             let uu____69561 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____69622 ->
                                   let uu____69635 = (e, c)  in
                                   (match uu____69635 with
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
                                                (fun uu____69675  ->
                                                   match uu____69675 with
                                                   | (x,uu____69681) ->
                                                       let uu____69682 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____69682)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____69700 =
                                                let uu____69702 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____69702
                                                 in
                                              if uu____69700
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
                                          let uu____69711 =
                                            let uu____69712 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____69712.FStar_Syntax_Syntax.n
                                             in
                                          match uu____69711 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____69737 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____69737 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____69748 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____69752 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____69752, gen_tvars))
                                in
                             (match uu____69561 with
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
        (let uu____69899 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____69899
         then
           let uu____69902 =
             let uu____69904 =
               FStar_List.map
                 (fun uu____69919  ->
                    match uu____69919 with
                    | (lb,uu____69928,uu____69929) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____69904 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____69902
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____69955  ->
                match uu____69955 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____69984 = gen env is_rec lecs  in
           match uu____69984 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____70083  ->
                       match uu____70083 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____70145 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____70145
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____70193  ->
                           match uu____70193 with
                           | (l,us,e,c,gvs) ->
                               let uu____70227 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____70229 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____70231 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____70233 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____70235 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____70227 uu____70229 uu____70231
                                 uu____70233 uu____70235))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____70280  ->
                match uu____70280 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____70324 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____70324, t, c, gvs)) univnames_lecs
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
              (let uu____70385 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____70385 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____70391 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _70394  -> FStar_Pervasives_Native.Some _70394)
                     uu____70391)
             in
          let is_var e1 =
            let uu____70402 =
              let uu____70403 = FStar_Syntax_Subst.compress e1  in
              uu____70403.FStar_Syntax_Syntax.n  in
            match uu____70402 with
            | FStar_Syntax_Syntax.Tm_name uu____70407 -> true
            | uu____70409 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1858_70430 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1858_70430.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1858_70430.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____70431 -> e2  in
          let env2 =
            let uu___1861_70433 = env1  in
            let uu____70434 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1861_70433.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1861_70433.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1861_70433.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1861_70433.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1861_70433.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1861_70433.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1861_70433.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1861_70433.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1861_70433.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1861_70433.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1861_70433.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1861_70433.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1861_70433.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1861_70433.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1861_70433.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1861_70433.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1861_70433.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____70434;
              FStar_TypeChecker_Env.is_iface =
                (uu___1861_70433.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1861_70433.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1861_70433.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1861_70433.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1861_70433.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1861_70433.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1861_70433.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1861_70433.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1861_70433.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1861_70433.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1861_70433.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1861_70433.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1861_70433.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1861_70433.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1861_70433.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1861_70433.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1861_70433.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1861_70433.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1861_70433.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1861_70433.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1861_70433.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1861_70433.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1861_70433.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1861_70433.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1861_70433.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____70436 = check1 env2 t1 t2  in
          match uu____70436 with
          | FStar_Pervasives_Native.None  ->
              let uu____70443 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____70449 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____70443 uu____70449
          | FStar_Pervasives_Native.Some g ->
              ((let uu____70456 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70456
                then
                  let uu____70461 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____70461
                else ());
               (let uu____70467 = decorate e t2  in (uu____70467, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____70495 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____70495
         then
           let uu____70498 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____70498
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____70512 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____70512
         then
           let uu____70520 = discharge g1  in
           let uu____70522 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____70520, uu____70522)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____70531 =
                let uu____70532 =
                  let uu____70533 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____70533
                    FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____70532
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____70531
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____70535 = destruct_comp c1  in
            match uu____70535 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____70553 = FStar_TypeChecker_Env.get_range env  in
                  let uu____70554 =
                    let uu____70559 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____70560 =
                      let uu____70561 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____70570 =
                        let uu____70581 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____70581]  in
                      uu____70561 :: uu____70570  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____70559 uu____70560  in
                  uu____70554 FStar_Pervasives_Native.None uu____70553  in
                ((let uu____70615 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____70615
                  then
                    let uu____70620 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____70620
                  else ());
                 (let g2 =
                    let uu____70626 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____70626  in
                  let uu____70627 = discharge g2  in
                  let uu____70629 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____70627, uu____70629)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___593_70663 =
        match uu___593_70663 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____70673)::[] -> f fst1
        | uu____70698 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____70710 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____70710
          (fun _70711  -> FStar_TypeChecker_Common.NonTrivial _70711)
         in
      let op_or_e e =
        let uu____70722 =
          let uu____70723 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____70723  in
        FStar_All.pipe_right uu____70722
          (fun _70726  -> FStar_TypeChecker_Common.NonTrivial _70726)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _70733  -> FStar_TypeChecker_Common.NonTrivial _70733)
         in
      let op_or_t t =
        let uu____70744 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____70744
          (fun _70747  -> FStar_TypeChecker_Common.NonTrivial _70747)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _70754  -> FStar_TypeChecker_Common.NonTrivial _70754)
         in
      let short_op_ite uu___594_70760 =
        match uu___594_70760 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____70770)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____70797)::[] ->
            let uu____70838 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____70838
              (fun _70839  -> FStar_TypeChecker_Common.NonTrivial _70839)
        | uu____70840 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____70852 =
          let uu____70860 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____70860)  in
        let uu____70868 =
          let uu____70878 =
            let uu____70886 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____70886)  in
          let uu____70894 =
            let uu____70904 =
              let uu____70912 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____70912)  in
            let uu____70920 =
              let uu____70930 =
                let uu____70938 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____70938)  in
              let uu____70946 =
                let uu____70956 =
                  let uu____70964 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____70964)  in
                [uu____70956; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____70930 :: uu____70946  in
            uu____70904 :: uu____70920  in
          uu____70878 :: uu____70894  in
        uu____70852 :: uu____70868  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____71026 =
            FStar_Util.find_map table
              (fun uu____71041  ->
                 match uu____71041 with
                 | (x,mk1) ->
                     let uu____71058 = FStar_Ident.lid_equals x lid  in
                     if uu____71058
                     then
                       let uu____71063 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____71063
                     else FStar_Pervasives_Native.None)
             in
          (match uu____71026 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____71067 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____71075 =
      let uu____71076 = FStar_Syntax_Util.un_uinst l  in
      uu____71076.FStar_Syntax_Syntax.n  in
    match uu____71075 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____71081 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____71117)::uu____71118 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____71137 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____71146,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____71147))::uu____71148 -> bs
      | uu____71166 ->
          let uu____71167 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____71167 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____71171 =
                 let uu____71172 = FStar_Syntax_Subst.compress t  in
                 uu____71172.FStar_Syntax_Syntax.n  in
               (match uu____71171 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____71176) ->
                    let uu____71197 =
                      FStar_Util.prefix_until
                        (fun uu___595_71237  ->
                           match uu___595_71237 with
                           | (uu____71245,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____71246)) ->
                               false
                           | uu____71251 -> true) bs'
                       in
                    (match uu____71197 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____71287,uu____71288) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____71360,uu____71361) ->
                         let uu____71434 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____71454  ->
                                   match uu____71454 with
                                   | (x,uu____71463) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____71434
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____71512  ->
                                     match uu____71512 with
                                     | (x,i) ->
                                         let uu____71531 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____71531, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____71542 -> bs))
  
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
            let uu____71571 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____71571
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
          let uu____71602 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____71602
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
        (let uu____71645 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____71645
         then
           ((let uu____71650 = FStar_Ident.text_of_lid lident  in
             d uu____71650);
            (let uu____71652 = FStar_Ident.text_of_lid lident  in
             let uu____71654 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____71652 uu____71654))
         else ());
        (let fv =
           let uu____71660 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____71660
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
         let uu____71672 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2019_71674 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2019_71674.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2019_71674.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2019_71674.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2019_71674.FStar_Syntax_Syntax.sigattrs)
           }), uu____71672))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___596_71692 =
        match uu___596_71692 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____71695 -> false  in
      let reducibility uu___597_71703 =
        match uu___597_71703 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____71710 -> false  in
      let assumption uu___598_71718 =
        match uu___598_71718 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____71722 -> false  in
      let reification uu___599_71730 =
        match uu___599_71730 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____71733 -> true
        | uu____71735 -> false  in
      let inferred uu___600_71743 =
        match uu___600_71743 with
        | FStar_Syntax_Syntax.Discriminator uu____71745 -> true
        | FStar_Syntax_Syntax.Projector uu____71747 -> true
        | FStar_Syntax_Syntax.RecordType uu____71753 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____71763 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____71776 -> false  in
      let has_eq uu___601_71784 =
        match uu___601_71784 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____71788 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____71867 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____71874 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____71885 =
        let uu____71887 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___602_71893  ->
                  match uu___602_71893 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____71896 -> false))
           in
        FStar_All.pipe_right uu____71887 Prims.op_Negation  in
      if uu____71885
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____71917 =
            let uu____71923 =
              let uu____71925 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____71925 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____71923)  in
          FStar_Errors.raise_error uu____71917 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____71943 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____71951 =
            let uu____71953 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____71953  in
          if uu____71951 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____71963),uu____71964) ->
              ((let uu____71976 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____71976
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____71985 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____71985
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____71996 ->
              let uu____72005 =
                let uu____72007 =
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
                Prims.op_Negation uu____72007  in
              if uu____72005 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____72017 ->
              let uu____72024 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____72024 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____72032 ->
              let uu____72039 =
                let uu____72041 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____72041  in
              if uu____72039 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____72051 ->
              let uu____72052 =
                let uu____72054 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____72054  in
              if uu____72052 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____72064 ->
              let uu____72065 =
                let uu____72067 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____72067  in
              if uu____72065 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____72077 ->
              let uu____72090 =
                let uu____72092 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____72092  in
              if uu____72090 then err'1 () else ()
          | uu____72102 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____72125 =
          let uu____72130 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____72130
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____72125
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____72149 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____72149
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____72167 =
                          let uu____72168 = FStar_Syntax_Subst.compress t1
                             in
                          uu____72168.FStar_Syntax_Syntax.n  in
                        match uu____72167 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____72174 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____72200 =
          let uu____72201 = FStar_Syntax_Subst.compress t1  in
          uu____72201.FStar_Syntax_Syntax.n  in
        match uu____72200 with
        | FStar_Syntax_Syntax.Tm_type uu____72205 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____72208 ->
            let uu____72223 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____72223 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____72256 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____72256
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____72262;
               FStar_Syntax_Syntax.index = uu____72263;
               FStar_Syntax_Syntax.sort = t2;_},uu____72265)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72274,uu____72275) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____72317::[]) ->
            let uu____72356 =
              let uu____72357 = FStar_Syntax_Util.un_uinst head1  in
              uu____72357.FStar_Syntax_Syntax.n  in
            (match uu____72356 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____72362 -> false)
        | uu____72364 -> false
      
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
        (let uu____72374 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____72374
         then
           let uu____72379 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____72379
         else ());
        res
       in aux g t
  