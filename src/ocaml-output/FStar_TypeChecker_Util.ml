open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____23 = FStar_TypeChecker_Env.get_range env  in
      let uu____24 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____23 uu____24
  
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
            FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun xs  ->
      fun g  ->
        let uu____85 =
          let uu____87 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____87  in
        if uu____85
        then g
        else
          (let uu____94 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____146  ->
                     match uu____146 with
                     | (uu____153,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____94 with
           | (solve_now,defer) ->
               ((let uu____188 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____188
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____205  ->
                         match uu____205 with
                         | (s,p) ->
                             let uu____215 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____215)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____230  ->
                         match uu____230 with
                         | (s,p) ->
                             let uu____240 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____240) defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___357_248 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___357_248.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___357_248.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___357_248.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___358_250 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___358_250.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___358_250.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___358_250.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____265 =
        let uu____267 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____267  in
      if uu____265
      then
        let us =
          let uu____272 =
            let uu____276 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____276
             in
          FStar_All.pipe_right uu____272 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____295 =
            let uu____301 =
              let uu____303 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____303
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____301)  in
          FStar_Errors.log_issue r uu____295);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____326  ->
      match uu____326 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____337;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____339;
          FStar_Syntax_Syntax.lbpos = uu____340;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____375 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____375 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____413) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____420) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____475) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____511 = FStar_Options.ml_ish ()  in
                                if uu____511
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____533 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____533
                            then
                              let uu____536 = FStar_Range.string_of_range r
                                 in
                              let uu____538 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____536 uu____538
                            else ());
                           FStar_Util.Inl t2)
                      | uu____543 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____545 = aux e1  in
                      match uu____545 with
                      | FStar_Util.Inr c ->
                          let uu____551 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____551
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____556 =
                               let uu____562 =
                                 let uu____564 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____564
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____562)
                                in
                             FStar_Errors.raise_error uu____556 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____573 ->
               let uu____574 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____574 with
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
    let pat_as_arg uu____638 =
      match uu____638 with
      | (p,i) ->
          let uu____658 = decorated_pattern_as_term p  in
          (match uu____658 with
           | (vars,te) ->
               let uu____681 =
                 let uu____686 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____686)  in
               (vars, uu____681))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____700 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____700)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____704 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____704)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____708 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____708)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____731 =
          let uu____750 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____750 FStar_List.unzip  in
        (match uu____731 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____888 =
               let uu____889 =
                 let uu____890 =
                   let uu____907 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____907, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____890  in
               mk1 uu____889  in
             (vars1, uu____888))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____946,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____956,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____970 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____981 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp
       in
    FStar_All.pipe_right uu____981 comp_univ_opt
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1010)::[] -> wp
      | uu____1035 ->
          let uu____1046 =
            let uu____1048 =
              let uu____1050 =
                FStar_List.map
                  (fun uu____1064  ->
                     match uu____1064 with
                     | (x,uu____1073) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____1050 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____1048
             in
          failwith uu____1046
       in
    let uu____1084 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1084, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____1101 = destruct_comp c  in
        match uu____1101 with
        | (u,uu____1109,wp) ->
            let uu____1111 =
              let uu____1122 =
                let uu____1131 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____1131  in
              [uu____1122]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____1111;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1164 =
          let uu____1171 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1172 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1171 uu____1172  in
        match uu____1164 with | (m,uu____1174,uu____1175) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1192 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____1192
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
        let uu____1239 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1239 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____1276 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____1276 with
             | (a,kwp) ->
                 let uu____1307 = destruct_comp m1  in
                 let uu____1314 = destruct_comp m2  in
                 ((md, a, kwp), uu____1307, uu____1314))
  
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
          fun flags1  ->
            let uu____1399 =
              let uu____1400 =
                let uu____1411 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1411]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1400;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1399
  
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
        fun flags1  ->
          let uu____1495 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1495
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
      let uu____1511 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____1511
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____1514  ->
           let uu____1515 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____1515)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1523 =
      let uu____1524 = FStar_Syntax_Subst.compress t  in
      uu____1524.FStar_Syntax_Syntax.n  in
    match uu____1523 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1528 -> true
    | uu____1544 -> false
  
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
              let uu____1614 =
                let uu____1616 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1616  in
              if uu____1614
              then f
              else (let uu____1623 = reason1 ()  in label uu____1623 r f)
  
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
            let uu___359_1644 = g  in
            let uu____1645 =
              let uu____1646 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1646  in
            {
              FStar_TypeChecker_Env.guard_f = uu____1645;
              FStar_TypeChecker_Env.deferred =
                (uu___359_1644.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___359_1644.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___359_1644.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1667 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1667
        then c
        else
          (let uu____1672 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1672
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____1736 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____1736]  in
                       let us =
                         let uu____1758 =
                           let uu____1761 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____1761]  in
                         u_res :: uu____1758  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____1767 =
                         let uu____1772 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____1773 =
                           let uu____1774 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____1783 =
                             let uu____1794 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____1803 =
                               let uu____1814 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____1814]  in
                             uu____1794 :: uu____1803  in
                           uu____1774 :: uu____1783  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1772 uu____1773
                          in
                       uu____1767 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1858 = destruct_comp c1  in
              match uu____1858 with
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
          (fun uu____1894  ->
             let uu____1895 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____1895)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___339_1907  ->
            match uu___339_1907 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1910 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit =
          let uu____1935 =
            let uu____1936 =
              let uu____1939 =
                FStar_Syntax_Util.arrow_formals_comp
                  lc.FStar_Syntax_Syntax.res_typ
                 in
              FStar_All.pipe_right uu____1939 FStar_Pervasives_Native.snd  in
            FStar_All.pipe_right uu____1936 FStar_Syntax_Util.comp_result  in
          FStar_All.pipe_right uu____1935 FStar_Syntax_Util.is_unit  in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit))
               &&
               (let uu____1986 = FStar_Syntax_Util.head_and_args' e  in
                match uu____1986 with
                | (head1,uu____2003) ->
                    let uu____2024 =
                      let uu____2025 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2025.FStar_Syntax_Syntax.n  in
                    (match uu____2024 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2030 =
                           let uu____2032 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2032
                            in
                         Prims.op_Negation uu____2030
                     | uu____2033 -> true)))
              &&
              (let uu____2036 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2036)
  
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
            let uu____2064 =
              let uu____2066 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2066  in
            if uu____2064
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2073 = FStar_Syntax_Util.is_unit t  in
               if uu____2073
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
                    let uu____2082 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2082
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2087 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2087 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2097 =
                             let uu____2098 =
                               let uu____2103 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2104 =
                                 let uu____2105 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2114 =
                                   let uu____2125 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2125]  in
                                 uu____2105 :: uu____2114  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2103
                                 uu____2104
                                in
                             uu____2098 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2097)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2161 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2161
           then
             let uu____2166 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2168 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2170 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2166 uu____2168 uu____2170
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags1  ->
    let uu____2187 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___340_2193  ->
              match uu___340_2193 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____2196 -> false))
       in
    if uu____2187
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___341_2208  ->
              match uu___341_2208 with
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
        let uu____2228 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2228
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____2234 = destruct_comp c1  in
           match uu____2234 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____2248 =
                   let uu____2253 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____2254 =
                     let uu____2255 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____2264 =
                       let uu____2275 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____2284 =
                         let uu____2295 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____2295]  in
                       uu____2275 :: uu____2284  in
                     uu____2255 :: uu____2264  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____2253 uu____2254  in
                 uu____2248 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____2338 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____2338)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2362 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____2364 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____2364
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____2370 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____2370 weaken
  
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
          fun flags1  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
               let uu____2418 = destruct_comp c1  in
               match uu____2418 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____2432 =
                       let uu____2437 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____2438 =
                         let uu____2439 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____2448 =
                           let uu____2459 =
                             let uu____2468 =
                               let uu____2469 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____2469 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____2468
                              in
                           let uu____2478 =
                             let uu____2489 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____2489]  in
                           uu____2459 :: uu____2478  in
                         uu____2439 :: uu____2448  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____2437 uu____2438
                        in
                     uu____2432 FStar_Pervasives_Native.None
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
      fun e_for_debugging_only  ->
        fun lc  ->
          fun g0  ->
            let uu____2577 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____2577
            then (lc, g0)
            else
              (let flags1 =
                 let uu____2589 =
                   let uu____2597 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____2597
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____2589 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____2627 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___342_2635  ->
                               match uu___342_2635 with
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
                               | uu____2638 -> []))
                        in
                     FStar_List.append flags1 uu____2627
                  in
               let strengthen uu____2644 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____2650 = FStar_TypeChecker_Env.guard_form g01  in
                    match uu____2650 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____2653 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____2653
                          then
                            let uu____2657 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____2659 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____2657 uu____2659
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____2664 =
                 let uu____2665 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____2665
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____2664,
                 (let uu___360_2667 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___360_2667.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___360_2667.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___360_2667.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___343_2676  ->
            match uu___343_2676 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____2680 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____2709 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____2709
          then e
          else
            (let uu____2716 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____2719 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____2719)
                in
             if uu____2716
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
          fun uu____2772  ->
            match uu____2772 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____2792 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____2792 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____2805 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____2805
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____2815 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____2815
                       then
                         let uu____2820 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____2820
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____2827 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____2827
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____2836 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____2836
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____2843 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____2843
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____2855 =
                  let uu____2856 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____2856
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
                       (fun uu____2873  ->
                          let uu____2874 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____2876 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____2881 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____2874 uu____2876 uu____2881);
                     (let aux uu____2899 =
                        let uu____2900 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____2900
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____2931 ->
                              let uu____2932 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____2932
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____2964 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____2964
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____3053 =
                              let uu____3059 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____3059, reason)  in
                            FStar_Util.Inl uu____3053
                        | uu____3069 -> aux ()  in
                      let try_simplify uu____3095 =
                        let maybe_close t x c =
                          let t1 =
                            FStar_TypeChecker_Normalize.normalize_refinement
                              FStar_TypeChecker_Normalize.whnf_steps env t
                             in
                          match t1.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_refine
                              ({ FStar_Syntax_Syntax.ppname = uu____3113;
                                 FStar_Syntax_Syntax.index = uu____3114;
                                 FStar_Syntax_Syntax.sort =
                                   {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_fvar fv;
                                     FStar_Syntax_Syntax.pos = uu____3116;
                                     FStar_Syntax_Syntax.vars = uu____3117;_};_},uu____3118)
                              when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____3126 -> c  in
                        let uu____3127 =
                          let uu____3129 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____3129  in
                        if uu____3127
                        then
                          let uu____3143 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____3143
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____3166 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____3166))
                        else
                          (let uu____3181 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____3181
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____3197 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____3197
                              then
                                let uu____3210 =
                                  let uu____3216 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____3216, "both gtot")  in
                                FStar_Util.Inl uu____3210
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____3247 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____3250 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____3250)
                                        in
                                     if uu____3247
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___361_3267 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___361_3267.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___361_3267.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____3268 =
                                         let uu____3274 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____3274, "c1 Tot")  in
                                       FStar_Util.Inl uu____3268
                                     else aux ()
                                 | uu____3285 -> aux ())))
                         in
                      let uu____3294 = try_simplify ()  in
                      match uu____3294 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____3320  ->
                                let uu____3321 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____3321);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____3335  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____3357 = lift_and_destruct env c11 c21
                                 in
                              match uu____3357 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____3410 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____3410]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____3430 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____3430]
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
                                    let uu____3477 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____3486 =
                                      let uu____3497 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____3506 =
                                        let uu____3517 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____3526 =
                                          let uu____3537 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____3546 =
                                            let uu____3557 =
                                              let uu____3566 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____3566
                                               in
                                            [uu____3557]  in
                                          uu____3537 :: uu____3546  in
                                        uu____3517 :: uu____3526  in
                                      uu____3497 :: uu____3506  in
                                    uu____3477 :: uu____3486  in
                                  let wp =
                                    let uu____3618 =
                                      let uu____3623 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____3623 wp_args
                                       in
                                    uu____3618 FStar_Pervasives_Native.None
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
                              let uu____3648 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____3648 with
                              | (m,uu____3656,lift2) ->
                                  let c23 =
                                    let uu____3659 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____3659
                                     in
                                  let uu____3660 = destruct_comp c12  in
                                  (match uu____3660 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____3674 =
                                           let uu____3679 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____3680 =
                                             let uu____3681 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____3690 =
                                               let uu____3701 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____3701]  in
                                             uu____3681 :: uu____3690  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____3679 uu____3680
                                            in
                                         uu____3674
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
                            let uu____3741 = destruct_comp c1_typ  in
                            match uu____3741 with
                            | (u_res_t1,res_t1,uu____3750) ->
                                let uu____3751 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____3751
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____3756 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____3756
                                   then
                                     (debug1
                                        (fun uu____3766  ->
                                           let uu____3767 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____3769 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____3767 uu____3769);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____3777 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____3780 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____3780)
                                         in
                                      if uu____3777
                                      then
                                        let e1' =
                                          let uu____3801 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____3801
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____3813  ->
                                              let uu____3814 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____3816 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____3814 uu____3816);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____3831  ->
                                              let uu____3832 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____3834 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____3832 uu____3834);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____3841 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____3841
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
      | uu____3859 -> g2
  
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
            (let uu____3883 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____3883)
           in
        let flags1 =
          if should_return1
          then
            let uu____3891 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____3891
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____3907 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____3911 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____3911
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____3917 =
              let uu____3919 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____3919  in
            (if uu____3917
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___362_3926 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___362_3926.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___362_3926.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___362_3926.FStar_Syntax_Syntax.effect_args);
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
               let uu____3939 =
                 let uu____3940 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____3940
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3939
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____3943 =
               let uu____3944 =
                 let uu____3945 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____3945
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____3944  in
             FStar_Syntax_Util.comp_set_flags uu____3943 flags1)
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
            fun uu____3983  ->
              match uu____3983 with
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
                    let uu____3995 =
                      ((let uu____3999 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____3999) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____3995
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____4017 =
        let uu____4018 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____4018  in
      FStar_Syntax_Syntax.fvar uu____4017 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Ident.lident,FStar_Syntax_Syntax.cflag
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
               fun uu____4088  ->
                 match uu____4088 with
                 | (uu____4102,eff_label,uu____4104,uu____4105) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____4118 =
          let uu____4126 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____4164  ->
                    match uu____4164 with
                    | (uu____4179,uu____4180,flags1,uu____4182) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___344_4199  ->
                                match uu___344_4199 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____4202 -> false))))
             in
          if uu____4126
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____4118 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____4235 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____4237 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4237
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____4278 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____4279 =
                     let uu____4284 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____4285 =
                       let uu____4286 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____4295 =
                         let uu____4306 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____4315 =
                           let uu____4326 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____4335 =
                             let uu____4346 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____4346]  in
                           uu____4326 :: uu____4335  in
                         uu____4306 :: uu____4315  in
                       uu____4286 :: uu____4295  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____4284 uu____4285  in
                   uu____4279 FStar_Pervasives_Native.None uu____4278  in
                 let default_case =
                   let post_k =
                     let uu____4401 =
                       let uu____4410 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____4410]  in
                     let uu____4429 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____4401 uu____4429  in
                   let kwp =
                     let uu____4435 =
                       let uu____4444 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____4444]  in
                     let uu____4463 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____4435 uu____4463  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____4470 =
                       let uu____4471 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____4471]  in
                     let uu____4490 =
                       let uu____4493 =
                         let uu____4500 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____4500
                          in
                       let uu____4501 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____4493 uu____4501  in
                     FStar_Syntax_Util.abs uu____4470 uu____4490
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
                   let uu____4525 =
                     should_not_inline_whole_match ||
                       (let uu____4528 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____4528)
                      in
                   if uu____4525 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____4567  ->
                        fun celse  ->
                          match uu____4567 with
                          | (g,eff_label,uu____4584,cthen) ->
                              let uu____4598 =
                                let uu____4623 =
                                  let uu____4624 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____4624
                                   in
                                lift_and_destruct env uu____4623 celse  in
                              (match uu____4598 with
                               | ((md,uu____4626,uu____4627),(uu____4628,uu____4629,wp_then),
                                  (uu____4631,uu____4632,wp_else)) ->
                                   let uu____4652 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____4652 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____4667::[] -> comp
                 | uu____4710 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____4729 = destruct_comp comp1  in
                     (match uu____4729 with
                      | (uu____4736,uu____4737,wp) ->
                          let wp1 =
                            let uu____4742 =
                              let uu____4747 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____4748 =
                                let uu____4749 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____4758 =
                                  let uu____4769 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____4769]  in
                                uu____4749 :: uu____4758  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____4747
                                uu____4748
                               in
                            uu____4742 FStar_Pervasives_Native.None
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
          let uu____4837 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____4837 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____4853 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____4859 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____4853 uu____4859
              else
                (let uu____4868 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____4874 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____4868 uu____4874)
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
          let uu____4899 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____4899
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____4902 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____4902
        then u_res
        else
          (let is_total =
             let uu____4909 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____4909
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____4920 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____4920 with
              | FStar_Pervasives_Native.None  ->
                  let uu____4923 =
                    let uu____4929 =
                      let uu____4931 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____4931
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____4929)
                     in
                  FStar_Errors.raise_error uu____4923
                    c.FStar_Syntax_Syntax.pos
              | FStar_Pervasives_Native.Some tm ->
                  env.FStar_TypeChecker_Env.universe_of env tm))
  
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
               let uu____4976 =
                 let uu____4977 = FStar_Syntax_Subst.compress t2  in
                 uu____4977.FStar_Syntax_Syntax.n  in
               match uu____4976 with
               | FStar_Syntax_Syntax.Tm_type uu____4981 -> true
               | uu____4983 -> false  in
             let uu____4985 =
               let uu____4986 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____4986.FStar_Syntax_Syntax.n  in
             match uu____4985 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____4994 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____5004 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____5004
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____5007 =
                     let uu____5008 =
                       let uu____5009 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____5009
                        in
                     (FStar_Pervasives_Native.None, uu____5008)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____5007
                    in
                 let e1 =
                   let uu____5015 =
                     let uu____5020 =
                       let uu____5021 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____5021]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5020  in
                   uu____5015 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____5048 -> (e, lc))
  
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
          (let uu____5083 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____5083
           then
             let uu____5086 = FStar_Syntax_Print.term_to_string e  in
             let uu____5088 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____5090 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____5086 uu____5088 uu____5090
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____5100 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____5100 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____5125 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____5151 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____5151, false)
             else
               (let uu____5161 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____5161, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____5174) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____5186 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____5186
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___363_5202 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___363_5202.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___363_5202.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___363_5202.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____5209 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____5209 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____5221 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let uu____5226 =
                        (let uu____5230 =
                           let uu____5231 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____5231
                             (FStar_TypeChecker_Env.norm_eff_name env)
                            in
                         FStar_All.pipe_right uu____5230
                           FStar_Syntax_Util.is_pure_or_ghost_effect)
                          ||
                          (let uu____5236 = FStar_Syntax_Util.eq_tm t res_t
                              in
                           uu____5236 = FStar_Syntax_Util.Equal)
                         in
                      if uu____5226
                      then
                        ((let uu____5239 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5239
                          then
                            let uu____5243 =
                              FStar_Syntax_Print.lid_to_string
                                (FStar_Syntax_Util.comp_effect_name c)
                               in
                            let uu____5245 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____5247 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print3
                              "weaken_result_type::strengthen_trivial: Not inserting the return since either the comp c:%s is pure/ghost or res_t:%s is same as t:%s\n"
                              uu____5243 uu____5245 uu____5247
                          else ());
                         FStar_Syntax_Util.set_result_typ c t)
                      else
                        (let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (res_t.FStar_Syntax_Syntax.pos)) res_t
                            in
                         let cret =
                           let uu____5256 = FStar_Syntax_Syntax.bv_to_name x
                              in
                           return_value env (comp_univ_opt c) res_t
                             uu____5256
                            in
                         let lc1 =
                           let uu____5258 = FStar_Syntax_Util.lcomp_of_comp c
                              in
                           let uu____5259 =
                             let uu____5260 =
                               FStar_Syntax_Util.lcomp_of_comp cret  in
                             ((FStar_Pervasives_Native.Some x), uu____5260)
                              in
                           bind e.FStar_Syntax_Syntax.pos env
                             (FStar_Pervasives_Native.Some e) uu____5258
                             uu____5259
                            in
                         (let uu____5264 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5264
                          then
                            let uu____5268 =
                              FStar_Syntax_Print.term_to_string e  in
                            let uu____5270 =
                              FStar_Syntax_Print.comp_to_string c  in
                            let uu____5272 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____5274 =
                              FStar_Syntax_Print.lcomp_to_string lc1  in
                            FStar_Util.print4
                              "weaken_result_type::strengthen_trivial: Inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                              uu____5268 uu____5270 uu____5272 uu____5274
                          else ());
                         (let uu____5279 = FStar_Syntax_Syntax.lcomp_comp lc1
                             in
                          FStar_Syntax_Util.set_result_typ uu____5279 t))
                       in
                    let lc1 =
                      FStar_Syntax_Syntax.mk_lcomp
                        lc.FStar_Syntax_Syntax.eff_name t
                        lc.FStar_Syntax_Syntax.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___364_5285 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___364_5285.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___364_5285.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___364_5285.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____5291 =
                      let uu____5292 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____5292
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____5298 =
                           let uu____5299 = FStar_Syntax_Subst.compress f1
                              in
                           uu____5299.FStar_Syntax_Syntax.n  in
                         match uu____5298 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____5302,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____5304;
                                           FStar_Syntax_Syntax.vars =
                                             uu____5305;_},uu____5306)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___365_5332 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___365_5332.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___365_5332.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___365_5332.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____5333 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____5336 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____5336
                               then
                                 let uu____5340 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____5342 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____5344 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____5346 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____5340 uu____5342 uu____5344
                                   uu____5346
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
                                   let uu____5359 =
                                     let uu____5364 =
                                       let uu____5365 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____5365]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____5364
                                      in
                                   uu____5359 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____5394 =
                                 let uu____5399 =
                                   FStar_All.pipe_left
                                     (fun _0_1  ->
                                        FStar_Pervasives_Native.Some _0_1)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____5420 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____5421 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____5422 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____5399
                                   uu____5420 e uu____5421 uu____5422
                                  in
                               match uu____5394 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___366_5426 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___366_5426.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___366_5426.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____5428 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____5428
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____5433 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____5433
                                     then
                                       let uu____5437 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____5437
                                     else ());
                                    c2))))
                       in
                    let flags1 =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___345_5450  ->
                              match uu___345_5450 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____5453 -> []))
                       in
                    let lc1 =
                      let uu____5455 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____5455 t flags1
                        strengthen
                       in
                    let g2 =
                      let uu___367_5457 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___367_5457.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___367_5457.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___367_5457.FStar_TypeChecker_Env.implicits)
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
        let uu____5493 =
          let uu____5496 =
            let uu____5501 =
              let uu____5502 =
                let uu____5511 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____5511  in
              [uu____5502]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____5501  in
          uu____5496 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____5493  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____5536 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____5536
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____5555 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____5571 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____5588 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____5588
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____5604)::(ens,uu____5606)::uu____5607 ->
                    let uu____5650 =
                      let uu____5653 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____5653  in
                    let uu____5654 =
                      let uu____5655 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____5655  in
                    (uu____5650, uu____5654)
                | uu____5658 ->
                    let uu____5669 =
                      let uu____5675 =
                        let uu____5677 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____5677
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____5675)
                       in
                    FStar_Errors.raise_error uu____5669
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____5697)::uu____5698 ->
                    let uu____5725 =
                      let uu____5730 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____5730
                       in
                    (match uu____5725 with
                     | (us_r,uu____5762) ->
                         let uu____5763 =
                           let uu____5768 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____5768
                            in
                         (match uu____5763 with
                          | (us_e,uu____5800) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____5803 =
                                  let uu____5804 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5804
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5803
                                  us_r
                                 in
                              let as_ens =
                                let uu____5806 =
                                  let uu____5807 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5807
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5806
                                  us_e
                                 in
                              let req =
                                let uu____5811 =
                                  let uu____5816 =
                                    let uu____5817 =
                                      let uu____5828 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____5828]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5817
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____5816
                                   in
                                uu____5811 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____5870 =
                                  let uu____5875 =
                                    let uu____5876 =
                                      let uu____5887 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____5887]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5876
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____5875
                                   in
                                uu____5870 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____5926 =
                                let uu____5929 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____5929  in
                              let uu____5930 =
                                let uu____5931 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____5931  in
                              (uu____5926, uu____5930)))
                | uu____5934 -> failwith "Impossible"))
  
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
      (let uu____5968 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____5968
       then
         let uu____5973 = FStar_Syntax_Print.term_to_string tm  in
         let uu____5975 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____5973 uu____5975
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
        (let uu____6029 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____6029
         then
           let uu____6034 = FStar_Syntax_Print.term_to_string tm  in
           let uu____6036 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6034
             uu____6036
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____6047 =
      let uu____6049 =
        let uu____6050 = FStar_Syntax_Subst.compress t  in
        uu____6050.FStar_Syntax_Syntax.n  in
      match uu____6049 with
      | FStar_Syntax_Syntax.Tm_app uu____6054 -> false
      | uu____6072 -> true  in
    if uu____6047
    then t
    else
      (let uu____6077 = FStar_Syntax_Util.head_and_args t  in
       match uu____6077 with
       | (head1,args) ->
           let uu____6120 =
             let uu____6122 =
               let uu____6123 = FStar_Syntax_Subst.compress head1  in
               uu____6123.FStar_Syntax_Syntax.n  in
             match uu____6122 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6128 -> false  in
           if uu____6120
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6160 ->
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
          ((let uu____6207 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____6207
            then
              let uu____6210 = FStar_Syntax_Print.term_to_string e  in
              let uu____6212 = FStar_Syntax_Print.term_to_string t  in
              let uu____6214 =
                let uu____6216 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____6216
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____6210 uu____6212 uu____6214
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____6229 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____6229 with
              | (formals,uu____6245) ->
                  let n_implicits =
                    let uu____6267 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____6345  ->
                              match uu____6345 with
                              | (uu____6353,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____6360 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____6360 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____6267 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____6487 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____6487 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____6515 =
                      let uu____6521 =
                        let uu____6523 = FStar_Util.string_of_int n_expected
                           in
                        let uu____6531 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____6533 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____6523 uu____6531 uu____6533
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____6521)
                       in
                    let uu____6543 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____6515 uu____6543
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___346_6571 =
              match uu___346_6571 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____6614 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____6614 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _0_2,uu____6732) when
                           _0_2 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____6777,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____6779))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6813 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____6813 with
                            | (v1,uu____6854,g) ->
                                ((let uu____6869 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____6869
                                  then
                                    let uu____6872 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____6872
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____6882 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____6882 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____6975 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____6975))))
                       | (uu____7002,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____7039 =
                             let uu____7052 =
                               let uu____7059 =
                                 let uu____7064 = FStar_Dyn.mkdyn env  in
                                 (uu____7064, tau)  in
                               FStar_Pervasives_Native.Some uu____7059  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____7052
                              in
                           (match uu____7039 with
                            | (v1,uu____7097,g) ->
                                ((let uu____7112 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____7112
                                  then
                                    let uu____7115 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____7115
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____7125 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____7125 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____7218 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____7218))))
                       | (uu____7245,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____7293 =
                       let uu____7320 = inst_n_binders t1  in
                       aux [] uu____7320 bs1  in
                     (match uu____7293 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____7392) -> (e, torig, guard)
                           | (uu____7423,[]) when
                               let uu____7454 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____7454 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____7456 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____7484 ->
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
            | uu____7497 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____7509 =
      let uu____7513 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____7513
        (FStar_List.map
           (fun u  ->
              let uu____7525 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____7525 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____7509 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____7553 = FStar_Util.set_is_empty x  in
      if uu____7553
      then []
      else
        (let s =
           let uu____7571 =
             let uu____7574 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____7574  in
           FStar_All.pipe_right uu____7571 FStar_Util.set_elements  in
         (let uu____7590 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____7590
          then
            let uu____7595 =
              let uu____7597 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____7597  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7595
          else ());
         (let r =
            let uu____7606 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____7606  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____7645 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____7645
                     then
                       let uu____7650 =
                         let uu____7652 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7652
                          in
                       let uu____7656 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____7658 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7650 uu____7656 uu____7658
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
        let uu____7688 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____7688 FStar_Util.set_elements  in
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
        | ([],uu____7727) -> generalized_univ_names
        | (uu____7734,[]) -> explicit_univ_names
        | uu____7741 ->
            let uu____7750 =
              let uu____7756 =
                let uu____7758 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____7758
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____7756)
               in
            FStar_Errors.raise_error uu____7750 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____7780 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____7780
       then
         let uu____7785 = FStar_Syntax_Print.term_to_string t  in
         let uu____7787 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____7785 uu____7787
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____7796 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____7796
        then
          let uu____7801 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____7801
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____7810 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____7810
         then
           let uu____7815 = FStar_Syntax_Print.term_to_string t  in
           let uu____7817 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____7815 uu____7817
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
        let uu____7901 =
          let uu____7903 =
            FStar_Util.for_all
              (fun uu____7917  ->
                 match uu____7917 with
                 | (uu____7927,uu____7928,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____7903  in
        if uu____7901
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____7980 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____7980
              then
                let uu____7983 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____7983
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____7990 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____7990
               then
                 let uu____7993 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7993
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____8011 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____8011 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____8045 =
             match uu____8045 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____8082 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____8082
                   then
                     let uu____8087 =
                       let uu____8089 =
                         let uu____8093 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____8093
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____8089
                         (FStar_String.concat ", ")
                        in
                     let uu____8141 =
                       let uu____8143 =
                         let uu____8147 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____8147
                           (FStar_List.map
                              (fun u  ->
                                 let uu____8160 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____8162 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____8160
                                   uu____8162))
                          in
                       FStar_All.pipe_right uu____8143
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8087
                       uu____8141
                   else ());
                  (let univs2 =
                     let uu____8176 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____8188 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____8188) univs1
                       uu____8176
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____8195 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____8195
                    then
                      let uu____8200 =
                        let uu____8202 =
                          let uu____8206 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____8206
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____8202
                          (FStar_String.concat ", ")
                         in
                      let uu____8254 =
                        let uu____8256 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____8270 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____8272 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____8270
                                    uu____8272))
                           in
                        FStar_All.pipe_right uu____8256
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8200
                        uu____8254
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____8293 =
             let uu____8310 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____8310  in
           match uu____8293 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8400 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____8400
                 then ()
                 else
                   (let uu____8405 = lec_hd  in
                    match uu____8405 with
                    | (lb1,uu____8413,uu____8414) ->
                        let uu____8415 = lec2  in
                        (match uu____8415 with
                         | (lb2,uu____8423,uu____8424) ->
                             let msg =
                               let uu____8427 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____8429 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8427 uu____8429
                                in
                             let uu____8432 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____8432))
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
                 let uu____8500 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____8500
                 then ()
                 else
                   (let uu____8505 = lec_hd  in
                    match uu____8505 with
                    | (lb1,uu____8513,uu____8514) ->
                        let uu____8515 = lec2  in
                        (match uu____8515 with
                         | (lb2,uu____8523,uu____8524) ->
                             let msg =
                               let uu____8527 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____8529 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8527 uu____8529
                                in
                             let uu____8532 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____8532))
                  in
               let lecs1 =
                 let uu____8543 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____8596 = univs_and_uvars_of_lec this_lec  in
                        match uu____8596 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8543 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____8701 = lec_hd  in
                   match uu____8701 with
                   | (lbname,e,c) ->
                       let uu____8711 =
                         let uu____8717 =
                           let uu____8719 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____8721 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____8723 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____8719 uu____8721 uu____8723
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____8717)
                          in
                       let uu____8727 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____8711 uu____8727
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____8746 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____8746 with
                         | FStar_Pervasives_Native.Some uu____8755 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____8763 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____8767 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____8767 with
                              | (bs,kres) ->
                                  ((let uu____8811 =
                                      let uu____8812 =
                                        let uu____8815 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine uu____8815
                                         in
                                      uu____8812.FStar_Syntax_Syntax.n  in
                                    match uu____8811 with
                                    | FStar_Syntax_Syntax.Tm_type uu____8816
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____8820 =
                                          let uu____8822 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____8822  in
                                        if uu____8820 then fail1 kres else ()
                                    | uu____8827 -> fail1 kres);
                                   (let a =
                                      let uu____8829 =
                                        let uu____8832 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_3  ->
                                             FStar_Pervasives_Native.Some
                                               _0_3) uu____8832
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____8829
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____8842 ->
                                          let uu____8851 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs uu____8851
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
                      (fun uu____8954  ->
                         match uu____8954 with
                         | (lbname,e,c) ->
                             let uu____9000 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9061 ->
                                   let uu____9074 = (e, c)  in
                                   (match uu____9074 with
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
                                                (fun uu____9114  ->
                                                   match uu____9114 with
                                                   | (x,uu____9120) ->
                                                       let uu____9121 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9121)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9139 =
                                                let uu____9141 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9141
                                                 in
                                              if uu____9139
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
                                          let uu____9150 =
                                            let uu____9151 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____9151.FStar_Syntax_Syntax.n
                                             in
                                          match uu____9150 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9176 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____9176 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9187 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____9191 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____9191, gen_tvars))
                                in
                             (match uu____9000 with
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
        (let uu____9338 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____9338
         then
           let uu____9341 =
             let uu____9343 =
               FStar_List.map
                 (fun uu____9358  ->
                    match uu____9358 with
                    | (lb,uu____9367,uu____9368) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____9343 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____9341
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9394  ->
                match uu____9394 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____9423 = gen env is_rec lecs  in
           match uu____9423 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9522  ->
                       match uu____9522 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____9584 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____9584
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____9632  ->
                           match uu____9632 with
                           | (l,us,e,c,gvs) ->
                               let uu____9666 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____9668 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____9670 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____9672 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____9674 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____9666 uu____9668 uu____9670 uu____9672
                                 uu____9674))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____9719  ->
                match uu____9719 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____9763 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____9763, t, c, gvs)) univnames_lecs
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
              (let uu____9824 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____9824 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____9830 = FStar_TypeChecker_Env.apply_guard f e  in
                   FStar_All.pipe_left
                     (fun _0_4  -> FStar_Pervasives_Native.Some _0_4)
                     uu____9830)
             in
          let is_var e1 =
            let uu____9840 =
              let uu____9841 = FStar_Syntax_Subst.compress e1  in
              uu____9841.FStar_Syntax_Syntax.n  in
            match uu____9840 with
            | FStar_Syntax_Syntax.Tm_name uu____9845 -> true
            | uu____9847 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___368_9868 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___368_9868.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___368_9868.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____9869 -> e2  in
          let env2 =
            let uu___369_9871 = env1  in
            let uu____9872 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___369_9871.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___369_9871.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___369_9871.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___369_9871.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___369_9871.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___369_9871.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___369_9871.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___369_9871.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___369_9871.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___369_9871.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___369_9871.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___369_9871.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___369_9871.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___369_9871.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___369_9871.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___369_9871.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___369_9871.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____9872;
              FStar_TypeChecker_Env.is_iface =
                (uu___369_9871.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___369_9871.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___369_9871.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___369_9871.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___369_9871.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___369_9871.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___369_9871.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___369_9871.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___369_9871.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___369_9871.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___369_9871.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___369_9871.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___369_9871.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___369_9871.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___369_9871.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___369_9871.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___369_9871.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___369_9871.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___369_9871.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___369_9871.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___369_9871.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___369_9871.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___369_9871.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___369_9871.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___369_9871.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____9874 = check1 env2 t1 t2  in
          match uu____9874 with
          | FStar_Pervasives_Native.None  ->
              let uu____9881 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____9887 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____9881 uu____9887
          | FStar_Pervasives_Native.Some g ->
              ((let uu____9894 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____9894
                then
                  let uu____9899 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____9899
                else ());
               (let uu____9905 = decorate e t2  in (uu____9905, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____9933 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____9933
         then
           let uu____9936 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____9936
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____9950 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____9950
         then
           let uu____9958 = discharge g1  in
           let uu____9960 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____9958, uu____9960)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____9969 =
                let uu____9970 =
                  let uu____9971 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____9971 FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____9970
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____9969
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____9973 = destruct_comp c1  in
            match uu____9973 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____9991 = FStar_TypeChecker_Env.get_range env  in
                  let uu____9992 =
                    let uu____9997 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____9998 =
                      let uu____9999 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____10008 =
                        let uu____10019 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____10019]  in
                      uu____9999 :: uu____10008  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____9997 uu____9998  in
                  uu____9992 FStar_Pervasives_Native.None uu____9991  in
                ((let uu____10055 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____10055
                  then
                    let uu____10060 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____10060
                  else ());
                 (let g2 =
                    let uu____10066 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____10066  in
                  let uu____10067 = discharge g2  in
                  let uu____10069 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____10067, uu____10069)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___347_10103 =
        match uu___347_10103 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10113)::[] -> f fst1
        | uu____10138 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____10150 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____10150
          (fun _0_5  -> FStar_TypeChecker_Common.NonTrivial _0_5)
         in
      let op_or_e e =
        let uu____10161 =
          let uu____10162 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____10162  in
        FStar_All.pipe_right uu____10161
          (fun _0_6  -> FStar_TypeChecker_Common.NonTrivial _0_6)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_7  -> FStar_TypeChecker_Common.NonTrivial _0_7)
         in
      let op_or_t t =
        let uu____10181 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____10181
          (fun _0_8  -> FStar_TypeChecker_Common.NonTrivial _0_8)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_9  -> FStar_TypeChecker_Common.NonTrivial _0_9)
         in
      let short_op_ite uu___348_10195 =
        match uu___348_10195 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10205)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10232)::[] ->
            let uu____10273 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____10273
              (fun _0_10  -> FStar_TypeChecker_Common.NonTrivial _0_10)
        | uu____10274 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____10286 =
          let uu____10294 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____10294)  in
        let uu____10302 =
          let uu____10312 =
            let uu____10320 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____10320)  in
          let uu____10328 =
            let uu____10338 =
              let uu____10346 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____10346)  in
            let uu____10354 =
              let uu____10364 =
                let uu____10372 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____10372)  in
              let uu____10380 =
                let uu____10390 =
                  let uu____10398 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____10398)  in
                [uu____10390; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____10364 :: uu____10380  in
            uu____10338 :: uu____10354  in
          uu____10312 :: uu____10328  in
        uu____10286 :: uu____10302  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____10460 =
            FStar_Util.find_map table
              (fun uu____10475  ->
                 match uu____10475 with
                 | (x,mk1) ->
                     let uu____10492 = FStar_Ident.lid_equals x lid  in
                     if uu____10492
                     then
                       let uu____10497 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____10497
                     else FStar_Pervasives_Native.None)
             in
          (match uu____10460 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10501 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____10509 =
      let uu____10510 = FStar_Syntax_Util.un_uinst l  in
      uu____10510.FStar_Syntax_Syntax.n  in
    match uu____10509 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10515 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10551)::uu____10552 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10571 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____10580,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10581))::uu____10582 -> bs
      | uu____10600 ->
          let uu____10601 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____10601 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10605 =
                 let uu____10606 = FStar_Syntax_Subst.compress t  in
                 uu____10606.FStar_Syntax_Syntax.n  in
               (match uu____10605 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10610) ->
                    let uu____10631 =
                      FStar_Util.prefix_until
                        (fun uu___349_10671  ->
                           match uu___349_10671 with
                           | (uu____10679,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10680)) ->
                               false
                           | uu____10685 -> true) bs'
                       in
                    (match uu____10631 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10721,uu____10722) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10794,uu____10795) ->
                         let uu____10868 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____10888  ->
                                   match uu____10888 with
                                   | (x,uu____10897) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____10868
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____10946  ->
                                     match uu____10946 with
                                     | (x,i) ->
                                         let uu____10965 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____10965, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____10976 -> bs))
  
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
            let uu____11005 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____11005
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
          let uu____11036 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____11036
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
        (let uu____11079 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____11079
         then
           ((let uu____11084 = FStar_Ident.text_of_lid lident  in
             d uu____11084);
            (let uu____11086 = FStar_Ident.text_of_lid lident  in
             let uu____11088 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____11086 uu____11088))
         else ());
        (let fv =
           let uu____11094 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11094
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
         let uu____11106 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___370_11108 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___370_11108.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___370_11108.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___370_11108.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___370_11108.FStar_Syntax_Syntax.sigattrs)
           }), uu____11106))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___350_11126 =
        match uu___350_11126 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11129 -> false  in
      let reducibility uu___351_11137 =
        match uu___351_11137 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11144 -> false  in
      let assumption uu___352_11152 =
        match uu___352_11152 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11156 -> false  in
      let reification uu___353_11164 =
        match uu___353_11164 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11167 -> true
        | uu____11169 -> false  in
      let inferred uu___354_11177 =
        match uu___354_11177 with
        | FStar_Syntax_Syntax.Discriminator uu____11179 -> true
        | FStar_Syntax_Syntax.Projector uu____11181 -> true
        | FStar_Syntax_Syntax.RecordType uu____11187 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11197 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11210 -> false  in
      let has_eq uu___355_11218 =
        match uu___355_11218 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11222 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____11301 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11308 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____11319 =
        let uu____11321 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___356_11327  ->
                  match uu___356_11327 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11330 -> false))
           in
        FStar_All.pipe_right uu____11321 Prims.op_Negation  in
      if uu____11319
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____11351 =
            let uu____11357 =
              let uu____11359 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11359 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11357)  in
          FStar_Errors.raise_error uu____11351 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____11377 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11385 =
            let uu____11387 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____11387  in
          if uu____11385 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11397),uu____11398) ->
              ((let uu____11410 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____11410
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11419 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____11419
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11430 ->
              let uu____11439 =
                let uu____11441 =
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
                Prims.op_Negation uu____11441  in
              if uu____11439 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11451 ->
              let uu____11458 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____11458 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11466 ->
              let uu____11473 =
                let uu____11475 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____11475  in
              if uu____11473 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11485 ->
              let uu____11486 =
                let uu____11488 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11488  in
              if uu____11486 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11498 ->
              let uu____11499 =
                let uu____11501 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11501  in
              if uu____11499 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11511 ->
              let uu____11524 =
                let uu____11526 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____11526  in
              if uu____11524 then err'1 () else ()
          | uu____11536 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____11559 =
          let uu____11564 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____11564
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____11559
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____11583 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____11583
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____11601 =
                          let uu____11602 = FStar_Syntax_Subst.compress t1
                             in
                          uu____11602.FStar_Syntax_Syntax.n  in
                        match uu____11601 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____11608 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____11634 =
          let uu____11635 = FStar_Syntax_Subst.compress t1  in
          uu____11635.FStar_Syntax_Syntax.n  in
        match uu____11634 with
        | FStar_Syntax_Syntax.Tm_type uu____11639 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____11642 ->
            let uu____11657 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____11657 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____11690 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____11690
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____11696;
               FStar_Syntax_Syntax.index = uu____11697;
               FStar_Syntax_Syntax.sort = t2;_},uu____11699)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____11708,uu____11709) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____11751::[]) ->
            let uu____11790 =
              let uu____11791 = FStar_Syntax_Util.un_uinst head1  in
              uu____11791.FStar_Syntax_Syntax.n  in
            (match uu____11790 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____11796 -> false)
        | uu____11798 -> false
      
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
        (let uu____11808 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____11808
         then
           let uu____11813 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____11813
         else ());
        res
       in aux g t
  