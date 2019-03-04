open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____65492 = FStar_TypeChecker_Env.get_range env  in
      let uu____65493 =
        FStar_TypeChecker_Err.failed_to_prove_specification errs  in
      FStar_Errors.log_issue uu____65492 uu____65493
  
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
        let uu____65554 =
          let uu____65556 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____65556  in
        if uu____65554
        then g
        else
          (let uu____65563 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____65615  ->
                     match uu____65615 with
                     | (uu____65622,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____65563 with
           | (solve_now,defer) ->
               ((let uu____65657 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____65657
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____65674  ->
                         match uu____65674 with
                         | (s,p) ->
                             let uu____65684 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____65684)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____65699  ->
                         match uu____65699 with
                         | (s,p) ->
                             let uu____65709 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____65709)
                      defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___631_65717 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___631_65717.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___631_65717.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___631_65717.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___634_65719 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___634_65719.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___634_65719.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___634_65719.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____65734 =
        let uu____65736 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____65736  in
      if uu____65734
      then
        let us =
          let uu____65741 =
            let uu____65745 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____65745
             in
          FStar_All.pipe_right uu____65741 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____65764 =
            let uu____65770 =
              let uu____65772 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____65772
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____65770)  in
          FStar_Errors.log_issue r uu____65764);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____65795  ->
      match uu____65795 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____65806;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____65808;
          FStar_Syntax_Syntax.lbpos = uu____65809;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____65844 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 e  in
               (match uu____65844 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____65882) ->
                          aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____65889)
                          -> FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____65944) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____65980 = FStar_Options.ml_ish ()  in
                                if uu____65980
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____66002 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____66002
                            then
                              let uu____66005 = FStar_Range.string_of_range r
                                 in
                              let uu____66007 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____66005 uu____66007
                            else ());
                           FStar_Util.Inl t2)
                      | uu____66012 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____66014 = aux e1  in
                      match uu____66014 with
                      | FStar_Util.Inr c ->
                          let uu____66020 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____66020
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____66025 =
                               let uu____66031 =
                                 let uu____66033 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____66033
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____66031)
                                in
                             FStar_Errors.raise_error uu____66025 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____66042 ->
               let uu____66043 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____66043 with
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
    let pat_as_arg uu____66107 =
      match uu____66107 with
      | (p,i) ->
          let uu____66127 = decorated_pattern_as_term p  in
          (match uu____66127 with
           | (vars,te) ->
               let uu____66150 =
                 let uu____66155 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____66155)  in
               (vars, uu____66150))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____66169 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____66169)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____66173 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____66173)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____66177 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____66177)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____66200 =
          let uu____66219 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____66219 FStar_List.unzip  in
        (match uu____66200 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____66357 =
               let uu____66358 =
                 let uu____66359 =
                   let uu____66376 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____66376, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____66359  in
               mk1 uu____66358  in
             (vars1, uu____66357))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____66415,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____66425,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____66439 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____66450 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp
       in
    FStar_All.pipe_right uu____66450 comp_univ_opt
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____66479)::[] -> wp
      | uu____66504 ->
          let uu____66515 =
            let uu____66517 =
              let uu____66519 =
                FStar_List.map
                  (fun uu____66533  ->
                     match uu____66533 with
                     | (x,uu____66542) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____66519 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____66517
             in
          failwith uu____66515
       in
    let uu____66553 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____66553, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____66570 = destruct_comp c  in
        match uu____66570 with
        | (u,uu____66578,wp) ->
            let uu____66580 =
              let uu____66591 =
                let uu____66600 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____66600  in
              [uu____66591]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____66580;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____66633 =
          let uu____66640 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____66641 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____66640 uu____66641  in
        match uu____66633 with | (m,uu____66643,uu____66644) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____66661 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____66661
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
        let uu____66708 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____66708 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____66745 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____66745 with
             | (a,kwp) ->
                 let uu____66776 = destruct_comp m1  in
                 let uu____66783 = destruct_comp m2  in
                 ((md, a, kwp), uu____66776, uu____66783))
  
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
            let uu____66868 =
              let uu____66869 =
                let uu____66880 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____66880]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____66869;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____66868
  
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
          let uu____66964 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____66964
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
      let uu____66980 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        uu____66980 lc.FStar_Syntax_Syntax.cflags
        (fun uu____66983  ->
           let uu____66984 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____66984)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____66992 =
      let uu____66993 = FStar_Syntax_Subst.compress t  in
      uu____66993.FStar_Syntax_Syntax.n  in
    match uu____66992 with
    | FStar_Syntax_Syntax.Tm_arrow uu____66997 -> true
    | uu____67013 -> false
  
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
              let uu____67083 =
                let uu____67085 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____67085  in
              if uu____67083
              then f
              else (let uu____67092 = reason1 ()  in label uu____67092 r f)
  
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
            let uu___828_67113 = g  in
            let uu____67114 =
              let uu____67115 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____67115  in
            {
              FStar_TypeChecker_Env.guard_f = uu____67114;
              FStar_TypeChecker_Env.deferred =
                (uu___828_67113.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___828_67113.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___828_67113.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____67136 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____67136
        then c
        else
          (let uu____67141 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____67141
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____67205 = FStar_Syntax_Syntax.mk_binder x
                            in
                         [uu____67205]  in
                       let us =
                         let uu____67227 =
                           let uu____67230 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____67230]  in
                         u_res :: uu____67227  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____67236 =
                         let uu____67241 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____67242 =
                           let uu____67243 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____67252 =
                             let uu____67263 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____67272 =
                               let uu____67283 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____67283]  in
                             uu____67263 :: uu____67272  in
                           uu____67243 :: uu____67252  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____67241
                           uu____67242
                          in
                       uu____67236 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____67327 = destruct_comp c1  in
              match uu____67327 with
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
          (fun uu____67363  ->
             let uu____67364 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____67364)
  
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
              ({ FStar_Syntax_Syntax.ppname = uu____67387;
                 FStar_Syntax_Syntax.index = uu____67388;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____67390;
                     FStar_Syntax_Syntax.vars = uu____67391;_};_},uu____67392)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____67400 -> c
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___585_67412  ->
            match uu___585_67412 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____67415 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit =
          let uu____67440 =
            let uu____67443 =
              FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____67443 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____67440
            (fun c  ->
               (let uu____67499 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____67499) &&
                 (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                    FStar_Syntax_Util.is_unit))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit))
               &&
               (let uu____67511 = FStar_Syntax_Util.head_and_args' e  in
                match uu____67511 with
                | (head1,uu____67528) ->
                    let uu____67549 =
                      let uu____67550 = FStar_Syntax_Util.un_uinst head1  in
                      uu____67550.FStar_Syntax_Syntax.n  in
                    (match uu____67549 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____67555 =
                           let uu____67557 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____67557
                            in
                         Prims.op_Negation uu____67555
                     | uu____67558 -> true)))
              &&
              (let uu____67561 = should_not_inline_lc lc  in
               Prims.op_Negation uu____67561)
  
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
            let uu____67589 =
              let uu____67591 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____67591  in
            if uu____67589
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____67598 = FStar_Syntax_Util.is_unit t  in
               if uu____67598
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
                    let uu____67607 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____67607
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____67612 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____67612 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____67622 =
                             let uu____67623 =
                               let uu____67628 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____67629 =
                                 let uu____67630 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____67639 =
                                   let uu____67650 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____67650]  in
                                 uu____67630 :: uu____67639  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____67628
                                 uu____67629
                                in
                             uu____67623 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env
                             uu____67622)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____67686 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____67686
           then
             let uu____67691 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____67693 = FStar_Syntax_Print.term_to_string v1  in
             let uu____67695 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____67691 uu____67693 uu____67695
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____67712 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___586_67718  ->
              match uu___586_67718 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____67721 -> false))
       in
    if uu____67712
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___587_67733  ->
              match uu___587_67733 with
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
        let uu____67753 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____67753
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____67759 = destruct_comp c1  in
           match uu____67759 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____67773 =
                   let uu____67778 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____67779 =
                     let uu____67780 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____67789 =
                       let uu____67800 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____67809 =
                         let uu____67820 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____67820]  in
                       uu____67800 :: uu____67809  in
                     uu____67780 :: uu____67789  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____67778 uu____67779  in
                 uu____67773 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____67863 = weaken_flags c1.FStar_Syntax_Syntax.flags
                  in
               mk_comp md u_res_t res_t wp1 uu____67863)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____67887 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____67889 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____67889
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____67895 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____67895 weaken
  
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
               let uu____67943 = destruct_comp c1  in
               match uu____67943 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____67957 =
                       let uu____67962 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____67963 =
                         let uu____67964 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____67973 =
                           let uu____67984 =
                             let uu____67993 =
                               let uu____67994 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____67994 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____67993
                              in
                           let uu____68003 =
                             let uu____68014 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____68014]  in
                           uu____67984 :: uu____68003  in
                         uu____67964 :: uu____67973  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____67962 uu____67963
                        in
                     uu____67957 FStar_Pervasives_Native.None
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
            let uu____68102 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____68102
            then (lc, g0)
            else
              (let flags =
                 let uu____68114 =
                   let uu____68122 =
                     FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
                   if uu____68122
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____68114 with
                 | (maybe_trivial_post,flags) ->
                     let uu____68152 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___588_68160  ->
                               match uu___588_68160 with
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
                               | uu____68163 -> []))
                        in
                     FStar_List.append flags uu____68152
                  in
               let strengthen uu____68169 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____68175 = FStar_TypeChecker_Env.guard_form g01
                       in
                    match uu____68175 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____68178 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____68178
                          then
                            let uu____68182 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____68184 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____68182 uu____68184
                          else ());
                         strengthen_comp env reason c f flags))
                  in
               let uu____68189 =
                 let uu____68190 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____68190
                   lc.FStar_Syntax_Syntax.res_typ flags strengthen
                  in
               (uu____68189,
                 (let uu___983_68192 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___983_68192.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___983_68192.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___983_68192.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___589_68201  ->
            match uu___589_68201 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____68205 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____68234 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____68234
          then e
          else
            (let uu____68241 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____68244 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____68244)
                in
             if uu____68241
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
          fun uu____68297  ->
            match uu____68297 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____68317 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____68317 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____68330 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____68330
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____68340 =
                         FStar_Syntax_Util.is_total_lcomp lc11  in
                       if uu____68340
                       then
                         let uu____68345 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____68345
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____68352 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____68352
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____68361 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____68361
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____68368 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____68368
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____68380 =
                  let uu____68381 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____68381
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
                       (fun uu____68398  ->
                          let uu____68399 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____68401 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____68406 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____68399 uu____68401 uu____68406);
                     (let aux uu____68424 =
                        let uu____68425 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____68425
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____68456 ->
                              let uu____68457 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____68457
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____68489 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____68489
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____68534 =
                        let uu____68535 =
                          let uu____68537 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____68537  in
                        if uu____68535
                        then
                          let uu____68551 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____68551
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____68574 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____68574))
                        else
                          (let uu____68589 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____68589
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___1049_68631 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1049_68631.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1049_68631.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____68632 =
                                 let uu____68638 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____68638, reason)  in
                               FStar_Util.Inl uu____68632  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____68674 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____68674
                                   (close1 x "c1 Tot")
                             | (uu____68688,FStar_Pervasives_Native.Some x)
                                 ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____68711,uu____68712) -> aux ()
                           else
                             (let uu____68727 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____68727
                              then
                                let uu____68740 =
                                  let uu____68746 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____68746, "both GTot")  in
                                FStar_Util.Inl uu____68740
                              else aux ()))
                         in
                      let uu____68757 = try_simplify ()  in
                      match uu____68757 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____68783  ->
                                let uu____68784 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____68784);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____68798  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____68820 = lift_and_destruct env c11 c21
                                 in
                              match uu____68820 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____68873 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____68873]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____68893 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____68893]
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
                                    let uu____68940 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____68949 =
                                      let uu____68960 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____68969 =
                                        let uu____68980 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____68989 =
                                          let uu____69000 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____69009 =
                                            let uu____69020 =
                                              let uu____69029 = mk_lam wp2
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____69029
                                               in
                                            [uu____69020]  in
                                          uu____69000 :: uu____69009  in
                                        uu____68980 :: uu____68989  in
                                      uu____68960 :: uu____68969  in
                                    uu____68940 :: uu____68949  in
                                  let wp =
                                    let uu____69081 =
                                      let uu____69086 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____69086 wp_args
                                       in
                                    uu____69081 FStar_Pervasives_Native.None
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
                              let uu____69111 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____69111 with
                              | (m,uu____69119,lift2) ->
                                  let c23 =
                                    let uu____69122 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____69122
                                     in
                                  let uu____69123 = destruct_comp c12  in
                                  (match uu____69123 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____69137 =
                                           let uu____69142 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____69143 =
                                             let uu____69144 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____69153 =
                                               let uu____69164 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____69164]  in
                                             uu____69144 :: uu____69153  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____69142 uu____69143
                                            in
                                         uu____69137
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
                            let uu____69204 = destruct_comp c1_typ  in
                            match uu____69204 with
                            | (u_res_t1,res_t1,uu____69213) ->
                                let uu____69214 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____69214
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____69219 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____69219
                                   then
                                     (debug1
                                        (fun uu____69229  ->
                                           let uu____69230 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____69232 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____69230 uu____69232);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____69240 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____69243 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____69243)
                                         in
                                      if uu____69240
                                      then
                                        let e1' =
                                          let uu____69264 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____69264
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____69276  ->
                                              let uu____69277 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____69279 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____69277 uu____69279);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____69294  ->
                                              let uu____69295 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____69297 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____69295 uu____69297);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____69304 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____69304
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
      | uu____69322 -> g2
  
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
            (let uu____69346 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____69346)
           in
        let flags =
          if should_return1
          then
            let uu____69354 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____69354
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____69370 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____69374 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____69374
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____69380 =
              let uu____69382 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____69382  in
            (if uu____69380
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___1168_69389 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___1168_69389.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___1168_69389.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___1168_69389.FStar_Syntax_Syntax.effect_args);
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
               let uu____69402 =
                 let uu____69403 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____69403
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                 uu____69402
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____69406 =
               let uu____69407 =
                 let uu____69408 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____69408
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____69407  in
             FStar_Syntax_Util.comp_set_flags uu____69406 flags)
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
            fun uu____69446  ->
              match uu____69446 with
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
                    let uu____69458 =
                      ((let uu____69462 = is_pure_or_ghost_effect env eff1
                           in
                        Prims.op_Negation uu____69462) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____69458
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____69480 =
        let uu____69481 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____69481  in
      FStar_Syntax_Syntax.fvar uu____69480 FStar_Syntax_Syntax.delta_constant
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
               fun uu____69551  ->
                 match uu____69551 with
                 | (uu____69565,eff_label,uu____69567,uu____69568) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____69581 =
          let uu____69589 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____69627  ->
                    match uu____69627 with
                    | (uu____69642,uu____69643,flags,uu____69645) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___590_69662  ->
                                match uu___590_69662 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____69665 -> false))))
             in
          if uu____69589
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____69581 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____69698 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____69700 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____69700
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____69741 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____69742 =
                     let uu____69747 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____69748 =
                       let uu____69749 = FStar_Syntax_Syntax.as_arg res_t1
                          in
                       let uu____69758 =
                         let uu____69769 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____69778 =
                           let uu____69789 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____69798 =
                             let uu____69809 =
                               FStar_Syntax_Syntax.as_arg wp_e  in
                             [uu____69809]  in
                           uu____69789 :: uu____69798  in
                         uu____69769 :: uu____69778  in
                       uu____69749 :: uu____69758  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____69747 uu____69748
                      in
                   uu____69742 FStar_Pervasives_Native.None uu____69741  in
                 let default_case =
                   let post_k =
                     let uu____69864 =
                       let uu____69873 =
                         FStar_Syntax_Syntax.null_binder res_t  in
                       [uu____69873]  in
                     let uu____69892 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____69864 uu____69892  in
                   let kwp =
                     let uu____69898 =
                       let uu____69907 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____69907]  in
                     let uu____69926 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____69898 uu____69926  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____69933 =
                       let uu____69934 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____69934]  in
                     let uu____69953 =
                       let uu____69956 =
                         let uu____69963 =
                           FStar_TypeChecker_Env.get_range env  in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____69963
                          in
                       let uu____69964 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____69956 uu____69964  in
                     FStar_Syntax_Util.abs uu____69933 uu____69953
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
                   let uu____69988 =
                     should_not_inline_whole_match ||
                       (let uu____69991 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____69991)
                      in
                   if uu____69988 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____70030  ->
                        fun celse  ->
                          match uu____70030 with
                          | (g,eff_label,uu____70047,cthen) ->
                              let uu____70061 =
                                let uu____70086 =
                                  let uu____70087 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____70087
                                   in
                                lift_and_destruct env uu____70086 celse  in
                              (match uu____70061 with
                               | ((md,uu____70089,uu____70090),(uu____70091,uu____70092,wp_then),
                                  (uu____70094,uu____70095,wp_else)) ->
                                   let uu____70115 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____70115 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____70130::[] -> comp
                 | uu____70173 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____70192 = destruct_comp comp1  in
                     (match uu____70192 with
                      | (uu____70199,uu____70200,wp) ->
                          let wp1 =
                            let uu____70205 =
                              let uu____70210 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____70211 =
                                let uu____70212 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____70221 =
                                  let uu____70232 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____70232]  in
                                uu____70212 :: uu____70221  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____70210
                                uu____70211
                               in
                            uu____70205 FStar_Pervasives_Native.None
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
          let uu____70300 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____70300 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____70316 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____70322 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____70316 uu____70322
              else
                (let uu____70331 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____70337 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____70331 uu____70337)
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
          let uu____70362 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____70362
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____70365 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____70365
        then u_res
        else
          (let is_total =
             let uu____70372 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____70372
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____70383 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____70383 with
              | FStar_Pervasives_Native.None  ->
                  let uu____70386 =
                    let uu____70392 =
                      let uu____70394 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____70394
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____70392)
                     in
                  FStar_Errors.raise_error uu____70386
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
               let uu____70439 =
                 let uu____70440 = FStar_Syntax_Subst.compress t2  in
                 uu____70440.FStar_Syntax_Syntax.n  in
               match uu____70439 with
               | FStar_Syntax_Syntax.Tm_type uu____70444 -> true
               | uu____70446 -> false  in
             let uu____70448 =
               let uu____70449 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____70449.FStar_Syntax_Syntax.n  in
             match uu____70448 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____70457 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____70467 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____70467
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____70470 =
                     let uu____70471 =
                       let uu____70472 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____70472
                        in
                     (FStar_Pervasives_Native.None, uu____70471)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____70470
                    in
                 let e1 =
                   let uu____70478 =
                     let uu____70483 =
                       let uu____70484 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____70484]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____70483  in
                   uu____70478 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____70511 -> (e, lc))
  
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
          (let uu____70546 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____70546
           then
             let uu____70549 = FStar_Syntax_Print.term_to_string e  in
             let uu____70551 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____70553 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____70549 uu____70551 uu____70553
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____70563 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____70563 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____70588 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____70614 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____70614, false)
             else
               (let uu____70624 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____70624, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____70637) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____70649 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____70649
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___1324_70665 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___1324_70665.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___1324_70665.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___1324_70665.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____70672 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____70672 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____70684 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t  in
                      let uu____70695 =
                        let uu____70697 = FStar_Syntax_Util.eq_tm t res_t  in
                        uu____70697 = FStar_Syntax_Util.Equal  in
                      if uu____70695
                      then
                        ((let uu____70700 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____70700
                          then
                            let uu____70704 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____70706 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____70704 uu____70706
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
                           | FStar_Syntax_Syntax.Tm_refine uu____70717 ->
                               true
                           | uu____70725 -> false  in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t
                              in
                           let cret =
                             let uu____70730 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             return_value env (comp_univ_opt c) res_t
                               uu____70730
                              in
                           let lc1 =
                             let uu____70732 =
                               FStar_Syntax_Util.lcomp_of_comp c  in
                             let uu____70733 =
                               let uu____70734 =
                                 FStar_Syntax_Util.lcomp_of_comp cret  in
                               ((FStar_Pervasives_Native.Some x),
                                 uu____70734)
                                in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____70732
                               uu____70733
                              in
                           ((let uu____70738 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____70738
                             then
                               let uu____70742 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____70744 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               let uu____70746 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____70748 =
                                 FStar_Syntax_Print.lcomp_to_string lc1  in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____70742 uu____70744 uu____70746
                                 uu____70748
                             else ());
                            (let uu____70753 =
                               FStar_Syntax_Syntax.lcomp_comp lc1  in
                             set_result_typ1 uu____70753))
                         else
                           ((let uu____70757 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____70757
                             then
                               let uu____70761 =
                                 FStar_Syntax_Print.term_to_string res_t  in
                               let uu____70763 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____70761 uu____70763
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
                      let uu___1356_70771 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1356_70771.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1356_70771.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1356_70771.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____70777 =
                      let uu____70778 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____70778
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____70784 =
                           let uu____70785 = FStar_Syntax_Subst.compress f1
                              in
                           uu____70785.FStar_Syntax_Syntax.n  in
                         match uu____70784 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____70788,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____70790;
                                            FStar_Syntax_Syntax.vars =
                                              uu____70791;_},uu____70792)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1372_70818 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___1372_70818.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___1372_70818.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___1372_70818.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____70819 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____70822 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____70822
                               then
                                 let uu____70826 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____70828 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____70830 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____70832 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____70826 uu____70828 uu____70830
                                   uu____70832
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
                                   let uu____70845 =
                                     let uu____70850 =
                                       let uu____70851 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____70851]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____70850
                                      in
                                   uu____70845 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____70880 =
                                 let uu____70885 =
                                   FStar_All.pipe_left
                                     (fun _70906  ->
                                        FStar_Pervasives_Native.Some _70906)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____70907 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____70908 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____70909 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____70885
                                   uu____70907 e uu____70908 uu____70909
                                  in
                               match uu____70880 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___1388_70913 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___1388_70913.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___1388_70913.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____70915 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____70915
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____70920 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____70920
                                     then
                                       let uu____70924 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____70924
                                     else ());
                                    c2))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___591_70937  ->
                              match uu___591_70937 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____70940 -> []))
                       in
                    let lc1 =
                      let uu____70942 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____70942 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1402_70944 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1402_70944.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1402_70944.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1402_70944.FStar_TypeChecker_Env.implicits)
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
        let uu____70980 =
          let uu____70983 =
            let uu____70988 =
              let uu____70989 =
                let uu____70998 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____70998  in
              [uu____70989]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____70988  in
          uu____70983 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____70980  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____71023 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____71023
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____71042 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____71058 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____71075 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____71075
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____71091)::(ens,uu____71093)::uu____71094 ->
                    let uu____71137 =
                      let uu____71140 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____71140  in
                    let uu____71141 =
                      let uu____71142 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____71142  in
                    (uu____71137, uu____71141)
                | uu____71145 ->
                    let uu____71156 =
                      let uu____71162 =
                        let uu____71164 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____71164
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____71162)
                       in
                    FStar_Errors.raise_error uu____71156
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____71184)::uu____71185 ->
                    let uu____71212 =
                      let uu____71217 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____71217
                       in
                    (match uu____71212 with
                     | (us_r,uu____71249) ->
                         let uu____71250 =
                           let uu____71255 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____71255
                            in
                         (match uu____71250 with
                          | (us_e,uu____71287) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____71290 =
                                  let uu____71291 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____71291
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____71290
                                  us_r
                                 in
                              let as_ens =
                                let uu____71293 =
                                  let uu____71294 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____71294
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____71293
                                  us_e
                                 in
                              let req =
                                let uu____71298 =
                                  let uu____71303 =
                                    let uu____71304 =
                                      let uu____71315 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____71315]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____71304
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____71303
                                   in
                                uu____71298 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____71357 =
                                  let uu____71362 =
                                    let uu____71363 =
                                      let uu____71374 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____71374]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____71363
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____71362
                                   in
                                uu____71357 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____71413 =
                                let uu____71416 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____71416  in
                              let uu____71417 =
                                let uu____71418 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____71418  in
                              (uu____71413, uu____71417)))
                | uu____71421 -> failwith "Impossible"))
  
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
      (let uu____71455 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____71455
       then
         let uu____71460 = FStar_Syntax_Print.term_to_string tm  in
         let uu____71462 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____71460
           uu____71462
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
        (let uu____71516 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____71516
         then
           let uu____71521 = FStar_Syntax_Print.term_to_string tm  in
           let uu____71523 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____71521
             uu____71523
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____71534 =
      let uu____71536 =
        let uu____71537 = FStar_Syntax_Subst.compress t  in
        uu____71537.FStar_Syntax_Syntax.n  in
      match uu____71536 with
      | FStar_Syntax_Syntax.Tm_app uu____71541 -> false
      | uu____71559 -> true  in
    if uu____71534
    then t
    else
      (let uu____71564 = FStar_Syntax_Util.head_and_args t  in
       match uu____71564 with
       | (head1,args) ->
           let uu____71607 =
             let uu____71609 =
               let uu____71610 = FStar_Syntax_Subst.compress head1  in
               uu____71610.FStar_Syntax_Syntax.n  in
             match uu____71609 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____71615 -> false  in
           if uu____71607
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____71647 ->
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
          ((let uu____71694 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____71694
            then
              let uu____71697 = FStar_Syntax_Print.term_to_string e  in
              let uu____71699 = FStar_Syntax_Print.term_to_string t  in
              let uu____71701 =
                let uu____71703 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____71703
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____71697 uu____71699 uu____71701
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____71716 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____71716 with
              | (formals,uu____71732) ->
                  let n_implicits =
                    let uu____71754 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____71832  ->
                              match uu____71832 with
                              | (uu____71840,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____71847 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____71847 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____71754 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____71974 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____71974 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____72002 =
                      let uu____72008 =
                        let uu____72010 = FStar_Util.string_of_int n_expected
                           in
                        let uu____72018 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____72020 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____72010 uu____72018 uu____72020
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____72008)
                       in
                    let uu____72030 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____72002 uu____72030
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___592_72058 =
              match uu___592_72058 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____72101 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____72101 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _72232,uu____72219)
                           when _72232 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____72265,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____72267))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____72301 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____72301 with
                            | (v1,uu____72342,g) ->
                                ((let uu____72357 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____72357
                                  then
                                    let uu____72360 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____72360
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____72370 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____72370 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____72463 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____72463))))
                       | (uu____72490,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____72527 =
                             let uu____72540 =
                               let uu____72547 =
                                 let uu____72552 = FStar_Dyn.mkdyn env  in
                                 (uu____72552, tau)  in
                               FStar_Pervasives_Native.Some uu____72547  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____72540
                              in
                           (match uu____72527 with
                            | (v1,uu____72585,g) ->
                                ((let uu____72600 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____72600
                                  then
                                    let uu____72603 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____72603
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____72613 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____72613 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____72706 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____72706))))
                       | (uu____72733,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____72781 =
                       let uu____72808 = inst_n_binders t1  in
                       aux [] uu____72808 bs1  in
                     (match uu____72781 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____72880) -> (e, torig, guard)
                           | (uu____72911,[]) when
                               let uu____72942 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____72942 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____72944 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____72972 ->
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
            | uu____72985 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____72997 =
      let uu____73001 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____73001
        (FStar_List.map
           (fun u  ->
              let uu____73013 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____73013 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____72997 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____73041 = FStar_Util.set_is_empty x  in
      if uu____73041
      then []
      else
        (let s =
           let uu____73059 =
             let uu____73062 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____73062  in
           FStar_All.pipe_right uu____73059 FStar_Util.set_elements  in
         (let uu____73078 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____73078
          then
            let uu____73083 =
              let uu____73085 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____73085  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____73083
          else ());
         (let r =
            let uu____73094 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____73094  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____73133 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____73133
                     then
                       let uu____73138 =
                         let uu____73140 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____73140
                          in
                       let uu____73144 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____73146 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____73138 uu____73144 uu____73146
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
        let uu____73176 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____73176 FStar_Util.set_elements  in
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
        | ([],uu____73215) -> generalized_univ_names
        | (uu____73222,[]) -> explicit_univ_names
        | uu____73229 ->
            let uu____73238 =
              let uu____73244 =
                let uu____73246 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____73246
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____73244)
               in
            FStar_Errors.raise_error uu____73238 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____73268 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____73268
       then
         let uu____73273 = FStar_Syntax_Print.term_to_string t  in
         let uu____73275 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____73273 uu____73275
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____73284 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____73284
        then
          let uu____73289 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____73289
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____73298 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____73298
         then
           let uu____73303 = FStar_Syntax_Print.term_to_string t  in
           let uu____73305 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____73303 uu____73305
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
        let uu____73389 =
          let uu____73391 =
            FStar_Util.for_all
              (fun uu____73405  ->
                 match uu____73405 with
                 | (uu____73415,uu____73416,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____73391  in
        if uu____73389
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____73468 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____73468
              then
                let uu____73471 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____73471
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____73478 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____73478
               then
                 let uu____73481 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____73481
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____73499 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____73499 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____73533 =
             match uu____73533 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____73570 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____73570
                   then
                     let uu____73575 =
                       let uu____73577 =
                         let uu____73581 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____73581
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____73577
                         (FStar_String.concat ", ")
                        in
                     let uu____73629 =
                       let uu____73631 =
                         let uu____73635 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____73635
                           (FStar_List.map
                              (fun u  ->
                                 let uu____73648 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____73650 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____73648
                                   uu____73650))
                          in
                       FStar_All.pipe_right uu____73631
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____73575
                       uu____73629
                   else ());
                  (let univs2 =
                     let uu____73664 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____73676 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____73676) univs1
                       uu____73664
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____73683 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____73683
                    then
                      let uu____73688 =
                        let uu____73690 =
                          let uu____73694 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____73694
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____73690
                          (FStar_String.concat ", ")
                         in
                      let uu____73742 =
                        let uu____73744 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____73758 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____73760 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____73758
                                    uu____73760))
                           in
                        FStar_All.pipe_right uu____73744
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____73688 uu____73742
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____73781 =
             let uu____73798 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____73798  in
           match uu____73781 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____73888 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____73888
                 then ()
                 else
                   (let uu____73893 = lec_hd  in
                    match uu____73893 with
                    | (lb1,uu____73901,uu____73902) ->
                        let uu____73903 = lec2  in
                        (match uu____73903 with
                         | (lb2,uu____73911,uu____73912) ->
                             let msg =
                               let uu____73915 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____73917 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____73915 uu____73917
                                in
                             let uu____73920 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____73920))
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
                 let uu____73988 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____73988
                 then ()
                 else
                   (let uu____73993 = lec_hd  in
                    match uu____73993 with
                    | (lb1,uu____74001,uu____74002) ->
                        let uu____74003 = lec2  in
                        (match uu____74003 with
                         | (lb2,uu____74011,uu____74012) ->
                             let msg =
                               let uu____74015 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____74017 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____74015 uu____74017
                                in
                             let uu____74020 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____74020))
                  in
               let lecs1 =
                 let uu____74031 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____74084 = univs_and_uvars_of_lec this_lec  in
                        match uu____74084 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____74031 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____74189 = lec_hd  in
                   match uu____74189 with
                   | (lbname,e,c) ->
                       let uu____74199 =
                         let uu____74205 =
                           let uu____74207 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____74209 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____74211 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____74207 uu____74209 uu____74211
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____74205)
                          in
                       let uu____74215 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____74199 uu____74215
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____74234 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____74234 with
                         | FStar_Pervasives_Native.Some uu____74243 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____74251 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____74255 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____74255 with
                              | (bs,kres) ->
                                  ((let uu____74299 =
                                      let uu____74300 =
                                        let uu____74303 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____74303
                                         in
                                      uu____74300.FStar_Syntax_Syntax.n  in
                                    match uu____74299 with
                                    | FStar_Syntax_Syntax.Tm_type uu____74304
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____74308 =
                                          let uu____74310 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____74310  in
                                        if uu____74308
                                        then fail1 kres
                                        else ()
                                    | uu____74315 -> fail1 kres);
                                   (let a =
                                      let uu____74317 =
                                        let uu____74320 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _74323  ->
                                             FStar_Pervasives_Native.Some
                                               _74323) uu____74320
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____74317
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____74331 ->
                                          let uu____74340 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____74340
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
                      (fun uu____74443  ->
                         match uu____74443 with
                         | (lbname,e,c) ->
                             let uu____74489 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____74550 ->
                                   let uu____74563 = (e, c)  in
                                   (match uu____74563 with
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
                                                (fun uu____74603  ->
                                                   match uu____74603 with
                                                   | (x,uu____74609) ->
                                                       let uu____74610 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____74610)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____74628 =
                                                let uu____74630 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____74630
                                                 in
                                              if uu____74628
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
                                          let uu____74639 =
                                            let uu____74640 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____74640.FStar_Syntax_Syntax.n
                                             in
                                          match uu____74639 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____74665 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____74665 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____74676 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____74680 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____74680, gen_tvars))
                                in
                             (match uu____74489 with
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
        (let uu____74827 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____74827
         then
           let uu____74830 =
             let uu____74832 =
               FStar_List.map
                 (fun uu____74847  ->
                    match uu____74847 with
                    | (lb,uu____74856,uu____74857) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____74832 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____74830
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____74883  ->
                match uu____74883 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____74912 = gen env is_rec lecs  in
           match uu____74912 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____75011  ->
                       match uu____75011 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____75073 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____75073
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____75121  ->
                           match uu____75121 with
                           | (l,us,e,c,gvs) ->
                               let uu____75155 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____75157 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____75159 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____75161 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____75163 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____75155 uu____75157 uu____75159
                                 uu____75161 uu____75163))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____75208  ->
                match uu____75208 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____75252 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____75252, t, c, gvs)) univnames_lecs
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
              (let uu____75313 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____75313 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____75319 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _75322  -> FStar_Pervasives_Native.Some _75322)
                     uu____75319)
             in
          let is_var e1 =
            let uu____75330 =
              let uu____75331 = FStar_Syntax_Subst.compress e1  in
              uu____75331.FStar_Syntax_Syntax.n  in
            match uu____75330 with
            | FStar_Syntax_Syntax.Tm_name uu____75335 -> true
            | uu____75337 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1858_75358 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1858_75358.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1858_75358.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____75359 -> e2  in
          let env2 =
            let uu___1861_75361 = env1  in
            let uu____75362 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1861_75361.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1861_75361.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1861_75361.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1861_75361.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1861_75361.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1861_75361.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1861_75361.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1861_75361.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1861_75361.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1861_75361.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1861_75361.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1861_75361.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1861_75361.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1861_75361.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1861_75361.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1861_75361.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1861_75361.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____75362;
              FStar_TypeChecker_Env.is_iface =
                (uu___1861_75361.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1861_75361.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1861_75361.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1861_75361.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1861_75361.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1861_75361.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1861_75361.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1861_75361.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1861_75361.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1861_75361.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1861_75361.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1861_75361.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1861_75361.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1861_75361.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1861_75361.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1861_75361.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1861_75361.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1861_75361.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1861_75361.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1861_75361.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1861_75361.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1861_75361.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1861_75361.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1861_75361.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1861_75361.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____75364 = check1 env2 t1 t2  in
          match uu____75364 with
          | FStar_Pervasives_Native.None  ->
              let uu____75371 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____75377 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____75371 uu____75377
          | FStar_Pervasives_Native.Some g ->
              ((let uu____75384 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____75384
                then
                  let uu____75389 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____75389
                else ());
               (let uu____75395 = decorate e t2  in (uu____75395, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____75423 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____75423
         then
           let uu____75426 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____75426
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____75440 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____75440
         then
           let uu____75448 = discharge g1  in
           let uu____75450 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____75448, uu____75450)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____75459 =
                let uu____75460 =
                  let uu____75461 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____75461
                    FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____75460
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____75459
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____75463 = destruct_comp c1  in
            match uu____75463 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____75481 = FStar_TypeChecker_Env.get_range env  in
                  let uu____75482 =
                    let uu____75487 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____75488 =
                      let uu____75489 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____75498 =
                        let uu____75509 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____75509]  in
                      uu____75489 :: uu____75498  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____75487 uu____75488  in
                  uu____75482 FStar_Pervasives_Native.None uu____75481  in
                ((let uu____75545 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____75545
                  then
                    let uu____75550 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____75550
                  else ());
                 (let g2 =
                    let uu____75556 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____75556  in
                  let uu____75557 = discharge g2  in
                  let uu____75559 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____75557, uu____75559)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___593_75593 =
        match uu___593_75593 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____75603)::[] -> f fst1
        | uu____75628 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____75640 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____75640
          (fun _75641  -> FStar_TypeChecker_Common.NonTrivial _75641)
         in
      let op_or_e e =
        let uu____75652 =
          let uu____75653 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____75653  in
        FStar_All.pipe_right uu____75652
          (fun _75656  -> FStar_TypeChecker_Common.NonTrivial _75656)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _75663  -> FStar_TypeChecker_Common.NonTrivial _75663)
         in
      let op_or_t t =
        let uu____75674 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____75674
          (fun _75677  -> FStar_TypeChecker_Common.NonTrivial _75677)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _75684  -> FStar_TypeChecker_Common.NonTrivial _75684)
         in
      let short_op_ite uu___594_75690 =
        match uu___594_75690 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____75700)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____75727)::[] ->
            let uu____75768 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____75768
              (fun _75769  -> FStar_TypeChecker_Common.NonTrivial _75769)
        | uu____75770 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____75782 =
          let uu____75790 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____75790)  in
        let uu____75798 =
          let uu____75808 =
            let uu____75816 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____75816)  in
          let uu____75824 =
            let uu____75834 =
              let uu____75842 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____75842)  in
            let uu____75850 =
              let uu____75860 =
                let uu____75868 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____75868)  in
              let uu____75876 =
                let uu____75886 =
                  let uu____75894 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____75894)  in
                [uu____75886; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____75860 :: uu____75876  in
            uu____75834 :: uu____75850  in
          uu____75808 :: uu____75824  in
        uu____75782 :: uu____75798  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____75956 =
            FStar_Util.find_map table
              (fun uu____75971  ->
                 match uu____75971 with
                 | (x,mk1) ->
                     let uu____75988 = FStar_Ident.lid_equals x lid  in
                     if uu____75988
                     then
                       let uu____75993 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____75993
                     else FStar_Pervasives_Native.None)
             in
          (match uu____75956 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____75997 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____76005 =
      let uu____76006 = FStar_Syntax_Util.un_uinst l  in
      uu____76006.FStar_Syntax_Syntax.n  in
    match uu____76005 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____76011 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____76047)::uu____76048 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____76067 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____76076,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____76077))::uu____76078 -> bs
      | uu____76096 ->
          let uu____76097 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____76097 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____76101 =
                 let uu____76102 = FStar_Syntax_Subst.compress t  in
                 uu____76102.FStar_Syntax_Syntax.n  in
               (match uu____76101 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____76106) ->
                    let uu____76127 =
                      FStar_Util.prefix_until
                        (fun uu___595_76167  ->
                           match uu___595_76167 with
                           | (uu____76175,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____76176)) ->
                               false
                           | uu____76181 -> true) bs'
                       in
                    (match uu____76127 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____76217,uu____76218) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____76290,uu____76291) ->
                         let uu____76364 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____76384  ->
                                   match uu____76384 with
                                   | (x,uu____76393) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____76364
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____76442  ->
                                     match uu____76442 with
                                     | (x,i) ->
                                         let uu____76461 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____76461, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____76472 -> bs))
  
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
            let uu____76501 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____76501
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
          let uu____76532 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____76532
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
        (let uu____76575 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____76575
         then
           ((let uu____76580 = FStar_Ident.text_of_lid lident  in
             d uu____76580);
            (let uu____76582 = FStar_Ident.text_of_lid lident  in
             let uu____76584 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____76582 uu____76584))
         else ());
        (let fv =
           let uu____76590 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____76590
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
         let uu____76602 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2019_76604 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2019_76604.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2019_76604.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2019_76604.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2019_76604.FStar_Syntax_Syntax.sigattrs)
           }), uu____76602))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___596_76622 =
        match uu___596_76622 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____76625 -> false  in
      let reducibility uu___597_76633 =
        match uu___597_76633 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____76640 -> false  in
      let assumption uu___598_76648 =
        match uu___598_76648 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____76652 -> false  in
      let reification uu___599_76660 =
        match uu___599_76660 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____76663 -> true
        | uu____76665 -> false  in
      let inferred uu___600_76673 =
        match uu___600_76673 with
        | FStar_Syntax_Syntax.Discriminator uu____76675 -> true
        | FStar_Syntax_Syntax.Projector uu____76677 -> true
        | FStar_Syntax_Syntax.RecordType uu____76683 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____76693 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____76706 -> false  in
      let has_eq uu___601_76714 =
        match uu___601_76714 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____76718 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____76797 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____76804 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____76815 =
        let uu____76817 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___602_76823  ->
                  match uu___602_76823 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____76826 -> false))
           in
        FStar_All.pipe_right uu____76817 Prims.op_Negation  in
      if uu____76815
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____76847 =
            let uu____76853 =
              let uu____76855 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____76855 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____76853)  in
          FStar_Errors.raise_error uu____76847 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____76873 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____76881 =
            let uu____76883 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____76883  in
          if uu____76881 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____76893),uu____76894) ->
              ((let uu____76906 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____76906
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____76915 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____76915
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____76926 ->
              let uu____76935 =
                let uu____76937 =
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
                Prims.op_Negation uu____76937  in
              if uu____76935 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____76947 ->
              let uu____76954 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____76954 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____76962 ->
              let uu____76969 =
                let uu____76971 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____76971  in
              if uu____76969 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____76981 ->
              let uu____76982 =
                let uu____76984 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____76984  in
              if uu____76982 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____76994 ->
              let uu____76995 =
                let uu____76997 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____76997  in
              if uu____76995 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____77007 ->
              let uu____77020 =
                let uu____77022 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____77022  in
              if uu____77020 then err'1 () else ()
          | uu____77032 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____77055 =
          let uu____77060 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____77060
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____77055
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____77079 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____77079
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____77097 =
                          let uu____77098 = FStar_Syntax_Subst.compress t1
                             in
                          uu____77098.FStar_Syntax_Syntax.n  in
                        match uu____77097 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____77104 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____77130 =
          let uu____77131 = FStar_Syntax_Subst.compress t1  in
          uu____77131.FStar_Syntax_Syntax.n  in
        match uu____77130 with
        | FStar_Syntax_Syntax.Tm_type uu____77135 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____77138 ->
            let uu____77153 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____77153 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____77186 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____77186
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____77192;
               FStar_Syntax_Syntax.index = uu____77193;
               FStar_Syntax_Syntax.sort = t2;_},uu____77195)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____77204,uu____77205) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____77247::[]) ->
            let uu____77286 =
              let uu____77287 = FStar_Syntax_Util.un_uinst head1  in
              uu____77287.FStar_Syntax_Syntax.n  in
            (match uu____77286 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____77292 -> false)
        | uu____77294 -> false
      
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
        (let uu____77304 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____77304
         then
           let uu____77309 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____77309
         else ());
        res
       in aux g t
  