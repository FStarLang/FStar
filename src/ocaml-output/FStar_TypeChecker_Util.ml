open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____21 = FStar_TypeChecker_Env.get_range env  in
      let uu____22 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____21 uu____22
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.ctx_uvar,FStar_Range.range)
                                      FStar_Pervasives_Native.tuple2
                                      Prims.list,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          FStar_TypeChecker_Env.new_implicit_var_aux reason r env k
            FStar_Syntax_Syntax.Strict
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun xs  ->
      fun g  ->
        let uu____74 =
          let uu____75 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____75  in
        if uu____74
        then g
        else
          (let uu____77 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____123  ->
                     match uu____123 with
                     | (uu____128,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____77 with
           | (solve_now,defer) ->
               ((let uu____157 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____157
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____168  ->
                         match uu____168 with
                         | (s,p) ->
                             let uu____175 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____175)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____186  ->
                         match uu____186 with
                         | (s,p) ->
                             let uu____193 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____193) defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___350_197 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___350_197.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___350_197.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___350_197.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___351_199 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___351_199.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___351_199.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___351_199.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____213 =
        let uu____214 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____214  in
      if uu____213
      then
        let us =
          let uu____216 =
            let uu____219 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____219
             in
          FStar_All.pipe_right uu____216 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____230 =
            let uu____235 =
              let uu____236 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____236
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____235)  in
          FStar_Errors.log_issue r uu____230);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____253  ->
      match uu____253 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____263;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____265;
          FStar_Syntax_Syntax.lbpos = uu____266;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____299 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____299 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____336) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____343) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____398) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____434 = FStar_Options.ml_ish ()  in
                                if uu____434
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____453 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____453
                            then
                              let uu____454 = FStar_Range.string_of_range r
                                 in
                              let uu____455 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____454 uu____455
                            else ());
                           FStar_Util.Inl t2)
                      | uu____457 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____459 = aux e1  in
                      match uu____459 with
                      | FStar_Util.Inr c ->
                          let uu____465 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____465
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____467 =
                               let uu____472 =
                                 let uu____473 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____473
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____472)
                                in
                             FStar_Errors.raise_error uu____467 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____477 ->
               let uu____478 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____478 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____537 =
      match uu____537 with
      | (p,i) ->
          let uu____554 = decorated_pattern_as_term p  in
          (match uu____554 with
           | (vars,te) ->
               let uu____577 =
                 let uu____582 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____582)  in
               (vars, uu____577))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____596 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____596)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____600 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____600)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____604 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____604)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____625 =
          let uu____644 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____644 FStar_List.unzip  in
        (match uu____625 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____780 =
               let uu____781 =
                 let uu____782 =
                   let uu____799 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____799, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____782  in
               mk1 uu____781  in
             (vars1, uu____780))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____837,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____847,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____861 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____883)::[] -> wp
      | uu____908 ->
          let uu____919 =
            let uu____920 =
              let uu____921 =
                FStar_List.map
                  (fun uu____933  ->
                     match uu____933 with
                     | (x,uu____941) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____921 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____920
             in
          failwith uu____919
       in
    let uu____948 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____948, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____964 = destruct_comp c  in
        match uu____964 with
        | (u,uu____972,wp) ->
            let uu____974 =
              let uu____985 =
                let uu____994 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____994  in
              [uu____985]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____974;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1026 =
          let uu____1033 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1034 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1033 uu____1034  in
        match uu____1026 with | (m,uu____1036,uu____1037) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1053 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____1053
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
  
let (lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,(FStar_Syntax_Syntax.universe,
                                            FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                                            FStar_Pervasives_Native.tuple3,
          (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.tuple3)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
        let uu____1096 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1096 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____1133 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____1133 with
             | (a,kwp) ->
                 let uu____1164 = destruct_comp m1  in
                 let uu____1171 = destruct_comp m2  in
                 ((md, a, kwp), uu____1164, uu____1171))
  
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
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags1  ->
            let uu____1251 =
              let uu____1252 =
                let uu____1263 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1263]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1252;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1251
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags1  ->
          let uu____1345 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1345
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1
  
let (subst_lcomp :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun subst1  ->
    fun lc  ->
      let uu____1357 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____1357
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____1360  ->
           let uu____1361 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____1361)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1367 =
      let uu____1368 = FStar_Syntax_Subst.compress t  in
      uu____1368.FStar_Syntax_Syntax.n  in
    match uu____1367 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1371 -> true
    | uu____1386 -> false
  
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
              let uu____1443 =
                let uu____1444 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1444  in
              if uu____1443
              then f
              else (let uu____1446 = reason1 ()  in label uu____1446 r f)
  
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
            let uu___352_1463 = g  in
            let uu____1464 =
              let uu____1465 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1465  in
            {
              FStar_TypeChecker_Env.guard_f = uu____1464;
              FStar_TypeChecker_Env.deferred =
                (uu___352_1463.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___352_1463.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___352_1463.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1485 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1485
        then c
        else
          (let uu____1487 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1487
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____1548 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____1548]  in
                       let us =
                         let uu____1570 =
                           let uu____1573 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____1573]  in
                         u_res :: uu____1570  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____1579 =
                         let uu____1584 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____1585 =
                           let uu____1586 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____1595 =
                             let uu____1606 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____1615 =
                               let uu____1626 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____1626]  in
                             uu____1606 :: uu____1615  in
                           uu____1586 :: uu____1595  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1584 uu____1585
                          in
                       uu____1579 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1670 = destruct_comp c1  in
              match uu____1670 with
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
          (fun uu____1705  ->
             let uu____1706 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____1706)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___332_1715  ->
            match uu___332_1715 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1716 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (let uu____1738 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____1738))
               &&
               (let uu____1745 = FStar_Syntax_Util.head_and_args' e  in
                match uu____1745 with
                | (head1,uu____1761) ->
                    let uu____1782 =
                      let uu____1783 = FStar_Syntax_Util.un_uinst head1  in
                      uu____1783.FStar_Syntax_Syntax.n  in
                    (match uu____1782 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____1787 =
                           let uu____1788 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____1788
                            in
                         Prims.op_Negation uu____1787
                     | uu____1789 -> true)))
              &&
              (let uu____1791 = should_not_inline_lc lc  in
               Prims.op_Negation uu____1791)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____1825 =
              let uu____1826 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____1826  in
            if uu____1825
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____1828 = FStar_Syntax_Util.is_unit t  in
               if uu____1828
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
                    let uu____1834 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____1834
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____1836 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____1836 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____1846 =
                             let uu____1847 =
                               let uu____1852 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____1853 =
                                 let uu____1854 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____1863 =
                                   let uu____1874 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____1874]  in
                                 uu____1854 :: uu____1863  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1852
                                 uu____1853
                                in
                             uu____1847 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____1846)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____1910 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____1910
           then
             let uu____1911 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____1912 = FStar_Syntax_Print.term_to_string v1  in
             let uu____1913 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____1911 uu____1912 uu____1913
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____1926 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___333_1930  ->
              match uu___333_1930 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____1931 -> false))
       in
    if uu____1926
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___334_1940  ->
              match uu___334_1940 with
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
        let uu____1959 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1959
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____1962 = destruct_comp c1  in
           match uu____1962 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____1976 =
                   let uu____1981 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____1982 =
                     let uu____1983 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____1992 =
                       let uu____2003 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____2012 =
                         let uu____2023 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____2023]  in
                       uu____2003 :: uu____2012  in
                     uu____1983 :: uu____1992  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____1981 uu____1982  in
                 uu____1976 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____2066 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____2066)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2089 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____2091 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____2091
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____2094 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____2094 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags1  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
               let uu____2137 = destruct_comp c1  in
               match uu____2137 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____2151 =
                       let uu____2156 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____2157 =
                         let uu____2158 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____2167 =
                           let uu____2178 =
                             let uu____2187 =
                               let uu____2188 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____2188 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____2187
                              in
                           let uu____2197 =
                             let uu____2208 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____2208]  in
                           uu____2178 :: uu____2197  in
                         uu____2158 :: uu____2167  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____2156 uu____2157
                        in
                     uu____2151 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos
                      in
                   mk_comp md u_res_t res_t wp1 flags1)
  
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun reason  ->
    fun env  ->
      fun e_for_debug_only  ->
        fun lc  ->
          fun g0  ->
            let uu____2293 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____2293
            then (lc, g0)
            else
              (let flags1 =
                 let uu____2302 =
                   let uu____2309 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____2309
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____2302 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____2329 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___335_2337  ->
                               match uu___335_2337 with
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
                               | uu____2340 -> []))
                        in
                     FStar_List.append flags1 uu____2329
                  in
               let strengthen uu____2346 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____2350 = FStar_TypeChecker_Env.guard_form g01  in
                    match uu____2350 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____2353 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____2353
                          then
                            let uu____2354 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____2355 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____2354 uu____2355
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____2357 =
                 let uu____2358 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____2358
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____2357,
                 (let uu___353_2360 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___353_2360.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___353_2360.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___353_2360.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___336_2367  ->
            match uu___336_2367 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____2368 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____2395 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____2395
          then e
          else
            (let uu____2399 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____2401 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____2401)
                in
             if uu____2399
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
          fun uu____2451  ->
            match uu____2451 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____2471 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____2471 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____2479 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____2479
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____2486 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____2486
                       then
                         let uu____2489 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____2489
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____2493 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____2493
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____2498 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____2498
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____2502 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____2502
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____2511 =
                  let uu____2512 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____2512
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
                       (fun uu____2526  ->
                          let uu____2527 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____2528 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____2530 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____2527 uu____2528 uu____2530);
                     (let aux uu____2544 =
                        let uu____2545 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____2545
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____2566 ->
                              let uu____2567 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____2567
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____2586 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____2586
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____2657 =
                              let uu____2662 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____2662, reason)  in
                            FStar_Util.Inl uu____2657
                        | uu____2669 -> aux ()  in
                      let try_simplify uu____2693 =
                        let maybe_close t x c =
                          let t1 =
                            FStar_TypeChecker_Normalize.normalize_refinement
                              FStar_TypeChecker_Normalize.whnf_steps env t
                             in
                          match t1.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_refine
                              ({ FStar_Syntax_Syntax.ppname = uu____2711;
                                 FStar_Syntax_Syntax.index = uu____2712;
                                 FStar_Syntax_Syntax.sort =
                                   {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_fvar fv;
                                     FStar_Syntax_Syntax.pos = uu____2714;
                                     FStar_Syntax_Syntax.vars = uu____2715;_};_},uu____2716)
                              when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____2723 -> c  in
                        let uu____2724 =
                          let uu____2725 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____2725  in
                        if uu____2724
                        then
                          let uu____2736 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____2736
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____2750 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____2750))
                        else
                          (let uu____2760 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____2760
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____2770 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____2770
                              then
                                let uu____2779 =
                                  let uu____2784 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____2784, "both gtot")  in
                                FStar_Util.Inl uu____2779
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____2808 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____2810 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____2810)
                                        in
                                     if uu____2808
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___354_2823 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___354_2823.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___354_2823.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____2824 =
                                         let uu____2829 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____2829, "c1 Tot")  in
                                       FStar_Util.Inl uu____2824
                                     else aux ()
                                 | uu____2835 -> aux ())))
                         in
                      let uu____2844 = try_simplify ()  in
                      match uu____2844 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____2864  ->
                                let uu____2865 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____2865);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____2874  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____2895 = lift_and_destruct env c11 c21
                                 in
                              match uu____2895 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____2948 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____2948]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____2968 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____2968]
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
                                    let uu____3015 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____3024 =
                                      let uu____3035 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____3044 =
                                        let uu____3055 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____3064 =
                                          let uu____3075 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____3084 =
                                            let uu____3095 =
                                              let uu____3104 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____3104
                                               in
                                            [uu____3095]  in
                                          uu____3075 :: uu____3084  in
                                        uu____3055 :: uu____3064  in
                                      uu____3035 :: uu____3044  in
                                    uu____3015 :: uu____3024  in
                                  let wp =
                                    let uu____3156 =
                                      let uu____3161 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____3161 wp_args
                                       in
                                    uu____3156 FStar_Pervasives_Native.None
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
                              let uu____3186 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____3186 with
                              | (m,uu____3194,lift2) ->
                                  let c23 =
                                    let uu____3197 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____3197
                                     in
                                  let uu____3198 = destruct_comp c12  in
                                  (match uu____3198 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____3212 =
                                           let uu____3217 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____3218 =
                                             let uu____3219 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____3228 =
                                               let uu____3239 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____3239]  in
                                             uu____3219 :: uu____3228  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____3217 uu____3218
                                            in
                                         uu____3212
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
                            let uu____3278 = destruct_comp c1_typ  in
                            match uu____3278 with
                            | (u_res_t1,res_t1,uu____3287) ->
                                let uu____3288 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____3288
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____3291 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____3291
                                   then
                                     (debug1
                                        (fun uu____3299  ->
                                           let uu____3300 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____3301 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____3300 uu____3301);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____3306 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____3308 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____3308)
                                         in
                                      if uu____3306
                                      then
                                        let e1' =
                                          let uu____3328 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____3328
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____3337  ->
                                              let uu____3338 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____3339 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____3338 uu____3339);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____3351  ->
                                              let uu____3352 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____3353 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____3352 uu____3353);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____3358 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____3358
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
      | uu____3374 -> g2
  
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
            (let uu____3396 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____3396)
           in
        let flags1 =
          if should_return1
          then
            let uu____3402 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____3402
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____3414 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____3418 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____3418
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____3422 =
              let uu____3423 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____3423  in
            (if uu____3422
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___355_3428 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___355_3428.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___355_3428.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___355_3428.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags1
                 }  in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags1)
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
               let uu____3439 =
                 let uu____3440 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____3440
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3439
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____3443 =
               let uu____3444 =
                 let uu____3445 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____3445
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____3444  in
             FStar_Syntax_Util.comp_set_flags uu____3443 flags1)
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags1 refine1
  
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
            fun uu____3480  ->
              match uu____3480 with
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
                    let uu____3492 =
                      ((let uu____3495 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____3495) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____3492
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____3509 =
        let uu____3510 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____3510  in
      FStar_Syntax_Syntax.fvar uu____3509 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                    Prims.list,Prims.bool ->
                                                                 FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple4 Prims.list ->
        FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____3576  ->
                 match uu____3576 with
                 | (uu____3589,eff_label,uu____3591,uu____3592) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____3603 =
          let uu____3610 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____3644  ->
                    match uu____3644 with
                    | (uu____3657,uu____3658,flags1,uu____3660) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___337_3674  ->
                                match uu___337_3674 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____3675 -> false))))
             in
          if uu____3610
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____3603 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____3698 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____3700 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____3700
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____3738 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3739 =
                     let uu____3744 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____3745 =
                       let uu____3746 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____3755 =
                         let uu____3766 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____3775 =
                           let uu____3786 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____3795 =
                             let uu____3806 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____3806]  in
                           uu____3786 :: uu____3795  in
                         uu____3766 :: uu____3775  in
                       uu____3746 :: uu____3755  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3744 uu____3745  in
                   uu____3739 FStar_Pervasives_Native.None uu____3738  in
                 let default_case =
                   let post_k =
                     let uu____3861 =
                       let uu____3870 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____3870]  in
                     let uu____3889 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____3861 uu____3889  in
                   let kwp =
                     let uu____3895 =
                       let uu____3904 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____3904]  in
                     let uu____3923 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____3895 uu____3923  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____3930 =
                       let uu____3931 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____3931]  in
                     let uu____3950 =
                       let uu____3953 =
                         let uu____3960 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____3960
                          in
                       let uu____3961 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____3953 uu____3961  in
                     FStar_Syntax_Util.abs uu____3930 uu____3950
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
                   let uu____3983 =
                     should_not_inline_whole_match ||
                       (let uu____3985 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____3985)
                      in
                   if uu____3983 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____4018  ->
                        fun celse  ->
                          match uu____4018 with
                          | (g,eff_label,uu____4034,cthen) ->
                              let uu____4046 =
                                let uu____4071 =
                                  let uu____4072 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____4072
                                   in
                                lift_and_destruct env uu____4071 celse  in
                              (match uu____4046 with
                               | ((md,uu____4074,uu____4075),(uu____4076,uu____4077,wp_then),
                                  (uu____4079,uu____4080,wp_else)) ->
                                   let uu____4100 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____4100 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____4114::[] -> comp
                 | uu____4154 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____4172 = destruct_comp comp1  in
                     (match uu____4172 with
                      | (uu____4179,uu____4180,wp) ->
                          let wp1 =
                            let uu____4185 =
                              let uu____4190 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____4191 =
                                let uu____4192 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____4201 =
                                  let uu____4212 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____4212]  in
                                uu____4192 :: uu____4201  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____4190
                                uu____4191
                               in
                            uu____4185 FStar_Pervasives_Native.None
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
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____4279 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____4279 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____4294 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____4299 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____4294 uu____4299
              else
                (let uu____4307 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____4312 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____4307 uu____4312)
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
            FStar_Pervasives_Native.tuple2)
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
               let uu____4356 =
                 let uu____4357 = FStar_Syntax_Subst.compress t2  in
                 uu____4357.FStar_Syntax_Syntax.n  in
               match uu____4356 with
               | FStar_Syntax_Syntax.Tm_type uu____4360 -> true
               | uu____4361 -> false  in
             let uu____4362 =
               let uu____4363 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____4363.FStar_Syntax_Syntax.n  in
             match uu____4362 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____4371 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____4381 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____4381
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____4383 =
                     let uu____4384 =
                       let uu____4385 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____4385
                        in
                     (FStar_Pervasives_Native.None, uu____4384)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____4383
                    in
                 let e1 =
                   let uu____4391 =
                     let uu____4396 =
                       let uu____4397 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____4397]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4396  in
                   uu____4391 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____4424 -> (e, lc))
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          (let uu____4458 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____4458
           then
             let uu____4459 = FStar_Syntax_Print.term_to_string e  in
             let uu____4460 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____4461 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____4459 uu____4460 uu____4461
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____4467 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____4467 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____4490 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____4512 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____4512, false)
             else
               (let uu____4518 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____4518, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____4529) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____4538 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____4538
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___356_4552 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___356_4552.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___356_4552.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___356_4552.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____4557 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____4557 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____4569 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let uu____4574 =
                        (let uu____4577 =
                           let uu____4578 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____4578
                             (FStar_TypeChecker_Env.norm_eff_name env)
                            in
                         FStar_All.pipe_right uu____4577
                           FStar_Syntax_Util.is_pure_or_ghost_effect)
                          ||
                          (let uu____4582 = FStar_Syntax_Util.eq_tm t res_t
                              in
                           uu____4582 = FStar_Syntax_Util.Equal)
                         in
                      if uu____4574
                      then
                        ((let uu____4584 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____4584
                          then
                            let uu____4585 =
                              FStar_Syntax_Print.lid_to_string
                                (FStar_Syntax_Util.comp_effect_name c)
                               in
                            let uu____4586 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____4587 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print3
                              "weaken_result_type::strengthen_trivial: Not inserting the return since either the comp c:%s is pure/ghost or res_t:%s is same as t:%s\n"
                              uu____4585 uu____4586 uu____4587
                          else ());
                         FStar_Syntax_Util.set_result_typ c t)
                      else
                        (let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (res_t.FStar_Syntax_Syntax.pos)) res_t
                            in
                         let cret =
                           let uu____4592 = FStar_Syntax_Syntax.bv_to_name x
                              in
                           return_value env (comp_univ_opt c) res_t
                             uu____4592
                            in
                         let lc1 =
                           let uu____4596 = FStar_Syntax_Util.lcomp_of_comp c
                              in
                           let uu____4597 =
                             let uu____4598 =
                               FStar_Syntax_Util.lcomp_of_comp cret  in
                             ((FStar_Pervasives_Native.Some x), uu____4598)
                              in
                           bind e.FStar_Syntax_Syntax.pos env
                             (FStar_Pervasives_Native.Some e) uu____4596
                             uu____4597
                            in
                         (let uu____4602 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____4602
                          then
                            let uu____4603 =
                              FStar_Syntax_Print.term_to_string e  in
                            let uu____4604 =
                              FStar_Syntax_Print.comp_to_string c  in
                            let uu____4605 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____4606 =
                              FStar_Syntax_Print.lcomp_to_string lc1  in
                            FStar_Util.print4
                              "weaken_result_type::strengthen_trivial: Inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                              uu____4603 uu____4604 uu____4605 uu____4606
                          else ());
                         (let uu____4608 = FStar_Syntax_Syntax.lcomp_comp lc1
                             in
                          FStar_Syntax_Util.set_result_typ uu____4608 t))
                       in
                    let lc1 =
                      FStar_Syntax_Syntax.mk_lcomp
                        lc.FStar_Syntax_Syntax.eff_name t
                        lc.FStar_Syntax_Syntax.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___357_4614 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___357_4614.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___357_4614.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___357_4614.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____4620 =
                      let uu____4621 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____4621
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____4624 =
                           let uu____4625 = FStar_Syntax_Subst.compress f1
                              in
                           uu____4625.FStar_Syntax_Syntax.n  in
                         match uu____4624 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____4628,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____4630;
                                           FStar_Syntax_Syntax.vars =
                                             uu____4631;_},uu____4632)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___358_4658 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___358_4658.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___358_4658.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___358_4658.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____4659 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____4662 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____4662
                               then
                                 let uu____4663 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____4664 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____4665 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____4666 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____4663 uu____4664 uu____4665
                                   uu____4666
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
                                   let uu____4675 =
                                     let uu____4680 =
                                       let uu____4681 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____4681]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____4680
                                      in
                                   uu____4675 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____4709 =
                                 let uu____4714 =
                                   FStar_All.pipe_left
                                     (fun _0_16  ->
                                        FStar_Pervasives_Native.Some _0_16)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____4731 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____4732 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____4733 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____4714
                                   uu____4731 e uu____4732 uu____4733
                                  in
                               match uu____4709 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___359_4737 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___359_4737.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___359_4737.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____4739 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____4739
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____4744 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____4744
                                     then
                                       let uu____4745 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____4745
                                     else ());
                                    c2))))
                       in
                    let flags1 =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___338_4755  ->
                              match uu___338_4755 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____4758 -> []))
                       in
                    let lc1 =
                      let uu____4760 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____4760 t flags1
                        strengthen
                       in
                    let g2 =
                      let uu___360_4762 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___360_4762.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___360_4762.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___360_4762.FStar_TypeChecker_Env.implicits)
                      }  in
                    (e, lc1, g2)))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____4797 =
          let uu____4800 =
            let uu____4805 =
              let uu____4806 =
                let uu____4815 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____4815  in
              [uu____4806]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4805  in
          uu____4800 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____4797  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____4840 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____4840
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4856 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4871 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____4887 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____4887
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4901)::(ens,uu____4903)::uu____4904 ->
                    let uu____4947 =
                      let uu____4950 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____4950  in
                    let uu____4951 =
                      let uu____4952 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____4952  in
                    (uu____4947, uu____4951)
                | uu____4955 ->
                    let uu____4966 =
                      let uu____4971 =
                        let uu____4972 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____4972
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____4971)
                       in
                    FStar_Errors.raise_error uu____4966
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4988)::uu____4989 ->
                    let uu____5016 =
                      let uu____5021 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____5021
                       in
                    (match uu____5016 with
                     | (us_r,uu____5053) ->
                         let uu____5054 =
                           let uu____5059 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____5059
                            in
                         (match uu____5054 with
                          | (us_e,uu____5091) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____5094 =
                                  let uu____5095 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5095
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5094
                                  us_r
                                 in
                              let as_ens =
                                let uu____5097 =
                                  let uu____5098 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5098
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5097
                                  us_e
                                 in
                              let req =
                                let uu____5102 =
                                  let uu____5107 =
                                    let uu____5108 =
                                      let uu____5119 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____5119]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5108
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____5107
                                   in
                                uu____5102 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____5161 =
                                  let uu____5166 =
                                    let uu____5167 =
                                      let uu____5178 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____5178]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5167
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____5166
                                   in
                                uu____5161 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____5217 =
                                let uu____5220 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____5220  in
                              let uu____5221 =
                                let uu____5222 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____5222  in
                              (uu____5217, uu____5221)))
                | uu____5225 -> failwith "Impossible"))
  
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
      (let uu____5257 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____5257
       then
         let uu____5258 = FStar_Syntax_Print.term_to_string tm  in
         let uu____5259 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____5258 uu____5259
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
        (let uu____5309 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____5309
         then
           let uu____5310 = FStar_Syntax_Print.term_to_string tm  in
           let uu____5311 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____5310
             uu____5311
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____5318 =
      let uu____5319 =
        let uu____5320 = FStar_Syntax_Subst.compress t  in
        uu____5320.FStar_Syntax_Syntax.n  in
      match uu____5319 with
      | FStar_Syntax_Syntax.Tm_app uu____5323 -> false
      | uu____5340 -> true  in
    if uu____5318
    then t
    else
      (let uu____5342 = FStar_Syntax_Util.head_and_args t  in
       match uu____5342 with
       | (head1,args) ->
           let uu____5385 =
             let uu____5386 =
               let uu____5387 = FStar_Syntax_Subst.compress head1  in
               uu____5387.FStar_Syntax_Syntax.n  in
             match uu____5386 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____5390 -> false  in
           if uu____5385
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____5420 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Env.trivial_guard)
        else
          ((let uu____5462 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____5462
            then
              let uu____5463 = FStar_Syntax_Print.term_to_string e  in
              let uu____5464 = FStar_Syntax_Print.term_to_string t  in
              let uu____5465 =
                let uu____5466 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____5466
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____5463 uu____5464 uu____5465
            else ());
           (let number_of_implicits t1 =
              let uu____5476 = FStar_Syntax_Util.arrow_formals t1  in
              match uu____5476 with
              | (formals,uu____5492) ->
                  let n_implicits =
                    let uu____5514 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____5592  ->
                              match uu____5592 with
                              | (uu____5599,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____5606 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____5606 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____5514 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____5732 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____5732 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____5756 =
                      let uu____5761 =
                        let uu____5762 = FStar_Util.string_of_int n_expected
                           in
                        let uu____5769 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____5770 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____5762 uu____5769 uu____5770
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____5761)
                       in
                    let uu____5777 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____5756 uu____5777
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___339_5800 =
              match uu___339_5800 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            match torig.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____5834 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____5834 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _0_17,uu____5949) when
                           _0_17 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____5992,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____5994))::rest)
                           ->
                           let t1 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6025 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t1
                              in
                           (match uu____6025 with
                            | (v1,uu____6065,g) ->
                                ((let uu____6080 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____6080
                                  then
                                    let uu____6081 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____6081
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____6088 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____6088 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____6181 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____6181))))
                       | (uu____6208,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t1 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6243 =
                             new_implicit_var
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t1
                              in
                           (match uu____6243 with
                            | (v1,uu____6283,g) ->
                                ((let uu____6298 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____6298
                                  then
                                    let uu____6299 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____6299
                                  else ());
                                 (let mark_meta_implicits tau1 g1 =
                                    let uu___361_6312 = g1  in
                                    let uu____6313 =
                                      FStar_List.map
                                        (fun imp  ->
                                           let uu___362_6319 = imp  in
                                           {
                                             FStar_TypeChecker_Env.imp_reason
                                               =
                                               (uu___362_6319.FStar_TypeChecker_Env.imp_reason);
                                             FStar_TypeChecker_Env.imp_uvar =
                                               (uu___362_6319.FStar_TypeChecker_Env.imp_uvar);
                                             FStar_TypeChecker_Env.imp_tm =
                                               (uu___362_6319.FStar_TypeChecker_Env.imp_tm);
                                             FStar_TypeChecker_Env.imp_range
                                               =
                                               (uu___362_6319.FStar_TypeChecker_Env.imp_range);
                                             FStar_TypeChecker_Env.imp_meta =
                                               (FStar_Pervasives_Native.Some
                                                  (env, tau1))
                                           })
                                        g1.FStar_TypeChecker_Env.implicits
                                       in
                                    {
                                      FStar_TypeChecker_Env.guard_f =
                                        (uu___361_6312.FStar_TypeChecker_Env.guard_f);
                                      FStar_TypeChecker_Env.deferred =
                                        (uu___361_6312.FStar_TypeChecker_Env.deferred);
                                      FStar_TypeChecker_Env.univ_ineqs =
                                        (uu___361_6312.FStar_TypeChecker_Env.univ_ineqs);
                                      FStar_TypeChecker_Env.implicits =
                                        uu____6313
                                    }  in
                                  let g1 = mark_meta_implicits tau g  in
                                  let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____6330 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____6330 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____6423 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____6423))))
                       | (uu____6450,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____6496 =
                       let uu____6523 = inst_n_binders t  in
                       aux [] uu____6523 bs1  in
                     (match uu____6496 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____6594) -> (e, torig, guard)
                           | (uu____6625,[]) when
                               let uu____6656 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____6656 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____6657 ->
                               let t1 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____6685 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t2 = FStar_Syntax_Subst.subst subst1 t1
                                  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t2, guard))))
            | uu____6698 -> (e, t, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____6708 =
      let uu____6711 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____6711
        (FStar_List.map
           (fun u  ->
              let uu____6721 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____6721 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____6708 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____6742 = FStar_Util.set_is_empty x  in
      if uu____6742
      then []
      else
        (let s =
           let uu____6757 =
             let uu____6760 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____6760  in
           FStar_All.pipe_right uu____6757 FStar_Util.set_elements  in
         (let uu____6776 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____6776
          then
            let uu____6777 =
              let uu____6778 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____6778  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____6777
          else ());
         (let r =
            let uu____6785 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____6785  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____6824 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____6824
                     then
                       let uu____6825 =
                         let uu____6826 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____6826
                          in
                       let uu____6827 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____6828 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____6825 uu____6827 uu____6828
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
        let uu____6854 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____6854 FStar_Util.set_elements  in
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
        | ([],uu____6892) -> generalized_univ_names
        | (uu____6899,[]) -> explicit_univ_names
        | uu____6906 ->
            let uu____6915 =
              let uu____6920 =
                let uu____6921 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____6921
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____6920)
               in
            FStar_Errors.raise_error uu____6915 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____6939 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____6939
       then
         let uu____6940 = FStar_Syntax_Print.term_to_string t  in
         let uu____6941 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____6940 uu____6941
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____6947 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____6947
        then
          let uu____6948 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____6948
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____6954 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____6954
         then
           let uu____6955 = FStar_Syntax_Print.term_to_string t  in
           let uu____6956 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____6955 uu____6956
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
         (univs2, ts))))
  
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_name Prims.list,
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder
                                                              Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____7034 =
          let uu____7035 =
            FStar_Util.for_all
              (fun uu____7048  ->
                 match uu____7048 with
                 | (uu____7057,uu____7058,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____7035  in
        if uu____7034
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____7106 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____7106
              then
                let uu____7107 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____7107
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____7111 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____7111
               then
                 let uu____7112 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7112
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____7127 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____7127 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____7161 =
             match uu____7161 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____7198 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____7198
                   then
                     let uu____7199 =
                       let uu____7200 =
                         let uu____7203 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____7203
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____7200
                         (FStar_String.concat ", ")
                        in
                     let uu____7246 =
                       let uu____7247 =
                         let uu____7250 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____7250
                           (FStar_List.map
                              (fun u  ->
                                 let uu____7261 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____7262 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____7261
                                   uu____7262))
                          in
                       FStar_All.pipe_right uu____7247
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____7199
                       uu____7246
                   else ());
                  (let univs2 =
                     let uu____7269 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____7281 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____7281) univs1
                       uu____7269
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____7288 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____7288
                    then
                      let uu____7289 =
                        let uu____7290 =
                          let uu____7293 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____7293
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____7290
                          (FStar_String.concat ", ")
                         in
                      let uu____7336 =
                        let uu____7337 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____7348 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____7349 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____7348
                                    uu____7349))
                           in
                        FStar_All.pipe_right uu____7337
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____7289
                        uu____7336
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____7363 =
             let uu____7380 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____7380  in
           match uu____7363 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____7470 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____7470
                 then ()
                 else
                   (let uu____7472 = lec_hd  in
                    match uu____7472 with
                    | (lb1,uu____7480,uu____7481) ->
                        let uu____7482 = lec2  in
                        (match uu____7482 with
                         | (lb2,uu____7490,uu____7491) ->
                             let msg =
                               let uu____7493 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____7494 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____7493 uu____7494
                                in
                             let uu____7495 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____7495))
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
                 let uu____7559 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____7559
                 then ()
                 else
                   (let uu____7561 = lec_hd  in
                    match uu____7561 with
                    | (lb1,uu____7569,uu____7570) ->
                        let uu____7571 = lec2  in
                        (match uu____7571 with
                         | (lb2,uu____7579,uu____7580) ->
                             let msg =
                               let uu____7582 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____7583 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____7582 uu____7583
                                in
                             let uu____7584 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____7584))
                  in
               let lecs1 =
                 let uu____7594 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____7647 = univs_and_uvars_of_lec this_lec  in
                        match uu____7647 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____7594 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____7748 = lec_hd  in
                   match uu____7748 with
                   | (lbname,e,c) ->
                       let uu____7758 =
                         let uu____7763 =
                           let uu____7764 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____7765 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____7766 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____7764 uu____7765 uu____7766
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____7763)
                          in
                       let uu____7767 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____7758 uu____7767
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____7788 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____7788 with
                         | FStar_Pervasives_Native.Some uu____7797 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____7804 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____7808 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____7808 with
                              | (bs,kres) ->
                                  ((let uu____7852 =
                                      let uu____7853 =
                                        let uu____7856 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine uu____7856
                                         in
                                      uu____7853.FStar_Syntax_Syntax.n  in
                                    match uu____7852 with
                                    | FStar_Syntax_Syntax.Tm_type uu____7857
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____7861 =
                                          let uu____7862 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____7862  in
                                        if uu____7861 then fail1 kres else ()
                                    | uu____7864 -> fail1 kres);
                                   (let a =
                                      let uu____7866 =
                                        let uu____7869 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_18  ->
                                             FStar_Pervasives_Native.Some
                                               _0_18) uu____7869
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____7866
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____7879 ->
                                          let uu____7888 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs uu____7888
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
                      (fun uu____7995  ->
                         match uu____7995 with
                         | (lbname,e,c) ->
                             let uu____8043 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____8118 ->
                                   let uu____8133 = (e, c)  in
                                   (match uu____8133 with
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
                                                (fun uu____8176  ->
                                                   match uu____8176 with
                                                   | (x,uu____8184) ->
                                                       let uu____8189 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____8189)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____8207 =
                                                let uu____8208 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____8208
                                                 in
                                              if uu____8207
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
                                          let uu____8214 =
                                            let uu____8215 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____8215.FStar_Syntax_Syntax.n
                                             in
                                          match uu____8214 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____8240 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____8240 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____8253 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____8257 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____8257, gen_tvars))
                                in
                             (match uu____8043 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____8411 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____8411
         then
           let uu____8412 =
             let uu____8413 =
               FStar_List.map
                 (fun uu____8426  ->
                    match uu____8426 with
                    | (lb,uu____8434,uu____8435) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____8413 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____8412
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____8456  ->
                match uu____8456 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____8485 = gen env is_rec lecs  in
           match uu____8485 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____8584  ->
                       match uu____8584 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____8646 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____8646
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____8692  ->
                           match uu____8692 with
                           | (l,us,e,c,gvs) ->
                               let uu____8726 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____8727 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____8728 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____8729 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____8730 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____8726 uu____8727 uu____8728 uu____8729
                                 uu____8730))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____8771  ->
                match uu____8771 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____8815 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____8815, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple2)
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
              (let uu____8872 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____8872 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____8878 = FStar_TypeChecker_Env.apply_guard f e  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____8878)
             in
          let is_var e1 =
            let uu____8887 =
              let uu____8888 = FStar_Syntax_Subst.compress e1  in
              uu____8888.FStar_Syntax_Syntax.n  in
            match uu____8887 with
            | FStar_Syntax_Syntax.Tm_name uu____8891 -> true
            | uu____8892 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___363_8912 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___363_8912.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___363_8912.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____8913 -> e2  in
          let env2 =
            let uu___364_8915 = env1  in
            let uu____8916 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___364_8915.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___364_8915.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___364_8915.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___364_8915.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___364_8915.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___364_8915.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___364_8915.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___364_8915.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___364_8915.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___364_8915.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___364_8915.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___364_8915.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___364_8915.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___364_8915.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___364_8915.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___364_8915.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___364_8915.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____8916;
              FStar_TypeChecker_Env.is_iface =
                (uu___364_8915.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___364_8915.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___364_8915.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___364_8915.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___364_8915.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___364_8915.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___364_8915.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___364_8915.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___364_8915.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___364_8915.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___364_8915.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___364_8915.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___364_8915.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___364_8915.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___364_8915.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___364_8915.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___364_8915.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___364_8915.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___364_8915.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___364_8915.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___364_8915.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___364_8915.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___364_8915.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___364_8915.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____8917 = check1 env2 t1 t2  in
          match uu____8917 with
          | FStar_Pervasives_Native.None  ->
              let uu____8924 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____8929 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____8924 uu____8929
          | FStar_Pervasives_Native.Some g ->
              ((let uu____8936 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____8936
                then
                  let uu____8937 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____8937
                else ());
               (let uu____8939 = decorate e t2  in (uu____8939, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____8964 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____8964
         then
           let uu____8965 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____8965
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____8975 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____8975
         then
           let uu____8980 = discharge g1  in
           let uu____8981 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____8980, uu____8981)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____8988 =
                let uu____8989 =
                  let uu____8990 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____8990 FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____8989
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____8988
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____8992 = destruct_comp c1  in
            match uu____8992 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____9009 = FStar_TypeChecker_Env.get_range env  in
                  let uu____9010 =
                    let uu____9015 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____9016 =
                      let uu____9017 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____9026 =
                        let uu____9037 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____9037]  in
                      uu____9017 :: uu____9026  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____9015 uu____9016  in
                  uu____9010 FStar_Pervasives_Native.None uu____9009  in
                ((let uu____9073 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____9073
                  then
                    let uu____9074 = FStar_Syntax_Print.term_to_string vc  in
                    FStar_Util.print1 "top-level VC: %s\n" uu____9074
                  else ());
                 (let g2 =
                    let uu____9077 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____9077  in
                  let uu____9078 = discharge g2  in
                  let uu____9079 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____9078, uu____9079)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___340_9111 =
        match uu___340_9111 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____9121)::[] -> f fst1
        | uu____9146 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____9157 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____9157
          (fun _0_20  -> FStar_TypeChecker_Common.NonTrivial _0_20)
         in
      let op_or_e e =
        let uu____9168 =
          let uu____9169 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____9169  in
        FStar_All.pipe_right uu____9168
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_or_t t =
        let uu____9188 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____9188
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let short_op_ite uu___341_9202 =
        match uu___341_9202 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____9212)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____9239)::[] ->
            let uu____9280 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____9280
              (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
        | uu____9281 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____9292 =
          let uu____9300 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____9300)  in
        let uu____9308 =
          let uu____9318 =
            let uu____9326 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____9326)  in
          let uu____9334 =
            let uu____9344 =
              let uu____9352 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____9352)  in
            let uu____9360 =
              let uu____9370 =
                let uu____9378 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____9378)  in
              let uu____9386 =
                let uu____9396 =
                  let uu____9404 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____9404)  in
                [uu____9396; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____9370 :: uu____9386  in
            uu____9344 :: uu____9360  in
          uu____9318 :: uu____9334  in
        uu____9292 :: uu____9308  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____9466 =
            FStar_Util.find_map table
              (fun uu____9481  ->
                 match uu____9481 with
                 | (x,mk1) ->
                     let uu____9498 = FStar_Ident.lid_equals x lid  in
                     if uu____9498
                     then
                       let uu____9501 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____9501
                     else FStar_Pervasives_Native.None)
             in
          (match uu____9466 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____9504 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____9510 =
      let uu____9511 = FStar_Syntax_Util.un_uinst l  in
      uu____9511.FStar_Syntax_Syntax.n  in
    match uu____9510 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____9515 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____9549)::uu____9550 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____9569 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____9578,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____9579))::uu____9580 -> bs
      | uu____9597 ->
          let uu____9598 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____9598 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____9602 =
                 let uu____9603 = FStar_Syntax_Subst.compress t  in
                 uu____9603.FStar_Syntax_Syntax.n  in
               (match uu____9602 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____9607) ->
                    let uu____9628 =
                      FStar_Util.prefix_until
                        (fun uu___342_9668  ->
                           match uu___342_9668 with
                           | (uu____9675,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9676)) ->
                               false
                           | uu____9679 -> true) bs'
                       in
                    (match uu____9628 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____9714,uu____9715) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____9787,uu____9788) ->
                         let uu____9861 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____9879  ->
                                   match uu____9879 with
                                   | (x,uu____9887) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____9861
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____9934  ->
                                     match uu____9934 with
                                     | (x,i) ->
                                         let uu____9953 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____9953, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____9963 -> bs))
  
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
            let uu____9991 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____9991
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
          let uu____10018 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____10018
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
        (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____10053 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____10053
         then
           ((let uu____10055 = FStar_Ident.text_of_lid lident  in
             d uu____10055);
            (let uu____10056 = FStar_Ident.text_of_lid lident  in
             let uu____10057 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____10056 uu____10057))
         else ());
        (let fv =
           let uu____10060 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____10060
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
         let uu____10070 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___365_10072 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___365_10072.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___365_10072.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___365_10072.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___365_10072.FStar_Syntax_Syntax.sigattrs)
           }), uu____10070))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___343_10088 =
        match uu___343_10088 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10089 -> false  in
      let reducibility uu___344_10095 =
        match uu___344_10095 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____10096 -> false  in
      let assumption uu___345_10102 =
        match uu___345_10102 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____10103 -> false  in
      let reification uu___346_10109 =
        match uu___346_10109 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____10110 -> true
        | uu____10111 -> false  in
      let inferred uu___347_10117 =
        match uu___347_10117 with
        | FStar_Syntax_Syntax.Discriminator uu____10118 -> true
        | FStar_Syntax_Syntax.Projector uu____10119 -> true
        | FStar_Syntax_Syntax.RecordType uu____10124 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____10133 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____10142 -> false  in
      let has_eq uu___348_10148 =
        match uu___348_10148 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____10149 -> false  in
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
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (visibility x))
                          || (reducibility x))
                         || (reification x))
                        || (inferred x))
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
        | FStar_Syntax_Syntax.Reflectable uu____10213 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10218 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____10228 =
        let uu____10229 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___349_10233  ->
                  match uu___349_10233 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____10234 -> false))
           in
        FStar_All.pipe_right uu____10229 Prims.op_Negation  in
      if uu____10228
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____10249 =
            let uu____10254 =
              let uu____10255 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____10255 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____10254)  in
          FStar_Errors.raise_error uu____10249 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____10267 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____10271 =
            let uu____10272 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____10272  in
          if uu____10271 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____10277),uu____10278) ->
              ((let uu____10288 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____10288
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____10292 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____10292
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____10298 ->
              let uu____10307 =
                let uu____10308 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          ((((x = FStar_Syntax_Syntax.Abstract) ||
                               (x = FStar_Syntax_Syntax.NoExtract))
                              || (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____10308  in
              if uu____10307 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____10314 ->
              let uu____10321 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____10321 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____10325 ->
              let uu____10332 =
                let uu____10333 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____10333  in
              if uu____10332 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____10339 ->
              let uu____10340 =
                let uu____10341 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____10341  in
              if uu____10340 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10347 ->
              let uu____10348 =
                let uu____10349 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____10349  in
              if uu____10348 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10355 ->
              let uu____10368 =
                let uu____10369 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____10369  in
              if uu____10368 then err'1 () else ()
          | uu____10375 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____10409 =
          let uu____10410 = FStar_Syntax_Subst.compress t1  in
          uu____10410.FStar_Syntax_Syntax.n  in
        match uu____10409 with
        | FStar_Syntax_Syntax.Tm_type uu____10413 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____10416 =
                 let uu____10421 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____10421
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____10416
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____10439 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____10439
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____10456 =
                                 let uu____10457 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____10457.FStar_Syntax_Syntax.n  in
                               match uu____10456 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____10461 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____10462 ->
            let uu____10477 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____10477 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____10509 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____10509
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____10511;
               FStar_Syntax_Syntax.index = uu____10512;
               FStar_Syntax_Syntax.sort = t2;_},uu____10514)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____10522,uu____10523) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____10565::[]) ->
            let uu____10604 =
              let uu____10605 = FStar_Syntax_Util.un_uinst head1  in
              uu____10605.FStar_Syntax_Syntax.n  in
            (match uu____10604 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____10609 -> false)
        | uu____10610 -> false
      
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
        (let uu____10618 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____10618
         then
           let uu____10619 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____10619
         else ());
        res
       in aux g t
  