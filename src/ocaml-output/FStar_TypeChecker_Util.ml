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
  
let (lcomp_univ_opt :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____871 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp
       in
    FStar_All.pipe_right uu____871 comp_univ_opt
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____899)::[] -> wp
      | uu____924 ->
          let uu____935 =
            let uu____936 =
              let uu____937 =
                FStar_List.map
                  (fun uu____949  ->
                     match uu____949 with
                     | (x,uu____957) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____937 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____936
             in
          failwith uu____935
       in
    let uu____964 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____964, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____980 = destruct_comp c  in
        match uu____980 with
        | (u,uu____988,wp) ->
            let uu____990 =
              let uu____1001 =
                let uu____1010 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____1010  in
              [uu____1001]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____990;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1042 =
          let uu____1049 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1050 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1049 uu____1050  in
        match uu____1042 with | (m,uu____1052,uu____1053) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1069 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____1069
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
        let uu____1112 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1112 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____1149 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____1149 with
             | (a,kwp) ->
                 let uu____1180 = destruct_comp m1  in
                 let uu____1187 = destruct_comp m2  in
                 ((md, a, kwp), uu____1180, uu____1187))
  
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
            let uu____1267 =
              let uu____1268 =
                let uu____1279 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1279]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1268;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1267
  
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
          let uu____1361 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1361
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
      let uu____1373 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____1373
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____1376  ->
           let uu____1377 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____1377)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1383 =
      let uu____1384 = FStar_Syntax_Subst.compress t  in
      uu____1384.FStar_Syntax_Syntax.n  in
    match uu____1383 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1387 -> true
    | uu____1402 -> false
  
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
              let uu____1459 =
                let uu____1460 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1460  in
              if uu____1459
              then f
              else (let uu____1462 = reason1 ()  in label uu____1462 r f)
  
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
            let uu___352_1479 = g  in
            let uu____1480 =
              let uu____1481 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1481  in
            {
              FStar_TypeChecker_Env.guard_f = uu____1480;
              FStar_TypeChecker_Env.deferred =
                (uu___352_1479.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___352_1479.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___352_1479.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1501 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1501
        then c
        else
          (let uu____1503 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1503
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____1564 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____1564]  in
                       let us =
                         let uu____1586 =
                           let uu____1589 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____1589]  in
                         u_res :: uu____1586  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____1595 =
                         let uu____1600 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____1601 =
                           let uu____1602 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____1611 =
                             let uu____1622 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____1631 =
                               let uu____1642 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____1642]  in
                             uu____1622 :: uu____1631  in
                           uu____1602 :: uu____1611  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1600 uu____1601
                          in
                       uu____1595 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1686 = destruct_comp c1  in
              match uu____1686 with
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
          (fun uu____1721  ->
             let uu____1722 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____1722)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___332_1731  ->
            match uu___332_1731 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1732 -> false))
  
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
                (let uu____1754 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____1754))
               &&
               (let uu____1761 = FStar_Syntax_Util.head_and_args' e  in
                match uu____1761 with
                | (head1,uu____1777) ->
                    let uu____1798 =
                      let uu____1799 = FStar_Syntax_Util.un_uinst head1  in
                      uu____1799.FStar_Syntax_Syntax.n  in
                    (match uu____1798 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____1803 =
                           let uu____1804 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____1804
                            in
                         Prims.op_Negation uu____1803
                     | uu____1805 -> true)))
              &&
              (let uu____1807 = should_not_inline_lc lc  in
               Prims.op_Negation uu____1807)
  
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
            let uu____1833 =
              let uu____1834 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____1834  in
            if uu____1833
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____1836 = FStar_Syntax_Util.is_unit t  in
               if uu____1836
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
                    let uu____1842 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____1842
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____1844 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____1844 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____1854 =
                             let uu____1855 =
                               let uu____1860 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____1861 =
                                 let uu____1862 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____1871 =
                                   let uu____1882 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____1882]  in
                                 uu____1862 :: uu____1871  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1860
                                 uu____1861
                                in
                             uu____1855 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____1854)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____1918 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____1918
           then
             let uu____1919 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____1920 = FStar_Syntax_Print.term_to_string v1  in
             let uu____1921 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____1919 uu____1920 uu____1921
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____1934 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___333_1938  ->
              match uu___333_1938 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____1939 -> false))
       in
    if uu____1934
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___334_1948  ->
              match uu___334_1948 with
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
        let uu____1967 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1967
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____1970 = destruct_comp c1  in
           match uu____1970 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____1984 =
                   let uu____1989 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____1990 =
                     let uu____1991 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____2000 =
                       let uu____2011 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____2020 =
                         let uu____2031 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____2031]  in
                       uu____2011 :: uu____2020  in
                     uu____1991 :: uu____2000  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____1989 uu____1990  in
                 uu____1984 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____2074 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____2074)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2097 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____2099 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____2099
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____2102 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____2102 weaken
  
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
               let uu____2145 = destruct_comp c1  in
               match uu____2145 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____2159 =
                       let uu____2164 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____2165 =
                         let uu____2166 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____2175 =
                           let uu____2186 =
                             let uu____2195 =
                               let uu____2196 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____2196 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____2195
                              in
                           let uu____2205 =
                             let uu____2216 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____2216]  in
                           uu____2186 :: uu____2205  in
                         uu____2166 :: uu____2175  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____2164 uu____2165
                        in
                     uu____2159 FStar_Pervasives_Native.None
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
            let uu____2301 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____2301
            then (lc, g0)
            else
              (let flags1 =
                 let uu____2310 =
                   let uu____2317 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____2317
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____2310 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____2337 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___335_2345  ->
                               match uu___335_2345 with
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
                               | uu____2348 -> []))
                        in
                     FStar_List.append flags1 uu____2337
                  in
               let strengthen uu____2354 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____2358 = FStar_TypeChecker_Env.guard_form g01  in
                    match uu____2358 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____2361 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____2361
                          then
                            let uu____2362 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____2363 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____2362 uu____2363
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____2365 =
                 let uu____2366 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____2366
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____2365,
                 (let uu___353_2368 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___353_2368.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___353_2368.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___353_2368.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___336_2375  ->
            match uu___336_2375 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____2376 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____2403 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____2403
          then e
          else
            (let uu____2407 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____2409 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____2409)
                in
             if uu____2407
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
          fun uu____2459  ->
            match uu____2459 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____2479 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____2479 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____2487 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____2487
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____2494 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____2494
                       then
                         let uu____2497 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____2497
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____2501 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____2501
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____2506 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____2506
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____2510 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____2510
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____2519 =
                  let uu____2520 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____2520
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
                       (fun uu____2534  ->
                          let uu____2535 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____2536 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____2538 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____2535 uu____2536 uu____2538);
                     (let aux uu____2552 =
                        let uu____2553 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____2553
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____2574 ->
                              let uu____2575 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____2575
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____2594 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____2594
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____2665 =
                              let uu____2670 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____2670, reason)  in
                            FStar_Util.Inl uu____2665
                        | uu____2677 -> aux ()  in
                      let try_simplify uu____2701 =
                        let maybe_close t x c =
                          let t1 =
                            FStar_TypeChecker_Normalize.normalize_refinement
                              FStar_TypeChecker_Normalize.whnf_steps env t
                             in
                          match t1.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_refine
                              ({ FStar_Syntax_Syntax.ppname = uu____2719;
                                 FStar_Syntax_Syntax.index = uu____2720;
                                 FStar_Syntax_Syntax.sort =
                                   {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_fvar fv;
                                     FStar_Syntax_Syntax.pos = uu____2722;
                                     FStar_Syntax_Syntax.vars = uu____2723;_};_},uu____2724)
                              when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____2731 -> c  in
                        let uu____2732 =
                          let uu____2733 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____2733  in
                        if uu____2732
                        then
                          let uu____2744 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____2744
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____2758 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____2758))
                        else
                          (let uu____2768 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____2768
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____2778 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____2778
                              then
                                let uu____2787 =
                                  let uu____2792 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____2792, "both gtot")  in
                                FStar_Util.Inl uu____2787
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____2816 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____2818 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____2818)
                                        in
                                     if uu____2816
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___354_2831 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___354_2831.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___354_2831.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____2832 =
                                         let uu____2837 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____2837, "c1 Tot")  in
                                       FStar_Util.Inl uu____2832
                                     else aux ()
                                 | uu____2843 -> aux ())))
                         in
                      let uu____2852 = try_simplify ()  in
                      match uu____2852 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____2872  ->
                                let uu____2873 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____2873);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____2882  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____2903 = lift_and_destruct env c11 c21
                                 in
                              match uu____2903 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____2956 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____2956]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____2976 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____2976]
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
                                    let uu____3023 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____3032 =
                                      let uu____3043 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____3052 =
                                        let uu____3063 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____3072 =
                                          let uu____3083 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____3092 =
                                            let uu____3103 =
                                              let uu____3112 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____3112
                                               in
                                            [uu____3103]  in
                                          uu____3083 :: uu____3092  in
                                        uu____3063 :: uu____3072  in
                                      uu____3043 :: uu____3052  in
                                    uu____3023 :: uu____3032  in
                                  let wp =
                                    let uu____3164 =
                                      let uu____3169 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____3169 wp_args
                                       in
                                    uu____3164 FStar_Pervasives_Native.None
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
                              let uu____3194 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____3194 with
                              | (m,uu____3202,lift2) ->
                                  let c23 =
                                    let uu____3205 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____3205
                                     in
                                  let uu____3206 = destruct_comp c12  in
                                  (match uu____3206 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____3220 =
                                           let uu____3225 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____3226 =
                                             let uu____3227 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____3236 =
                                               let uu____3247 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____3247]  in
                                             uu____3227 :: uu____3236  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____3225 uu____3226
                                            in
                                         uu____3220
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
                            let uu____3286 = destruct_comp c1_typ  in
                            match uu____3286 with
                            | (u_res_t1,res_t1,uu____3295) ->
                                let uu____3296 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____3296
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____3299 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____3299
                                   then
                                     (debug1
                                        (fun uu____3307  ->
                                           let uu____3308 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____3309 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____3308 uu____3309);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____3314 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____3316 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____3316)
                                         in
                                      if uu____3314
                                      then
                                        let e1' =
                                          let uu____3336 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____3336
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____3345  ->
                                              let uu____3346 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____3347 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____3346 uu____3347);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____3359  ->
                                              let uu____3360 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____3361 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____3360 uu____3361);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____3366 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____3366
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
      | uu____3382 -> g2
  
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
            (let uu____3404 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____3404)
           in
        let flags1 =
          if should_return1
          then
            let uu____3410 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____3410
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____3422 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____3426 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____3426
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____3430 =
              let uu____3431 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____3431  in
            (if uu____3430
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___355_3436 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___355_3436.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___355_3436.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___355_3436.FStar_Syntax_Syntax.effect_args);
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
               let uu____3447 =
                 let uu____3448 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____3448
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____3447
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____3451 =
               let uu____3452 =
                 let uu____3453 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____3453
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____3452  in
             FStar_Syntax_Util.comp_set_flags uu____3451 flags1)
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
            fun uu____3488  ->
              match uu____3488 with
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
                    let uu____3500 =
                      ((let uu____3503 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____3503) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____3500
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____3517 =
        let uu____3518 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____3518  in
      FStar_Syntax_Syntax.fvar uu____3517 FStar_Syntax_Syntax.delta_constant
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
               fun uu____3584  ->
                 match uu____3584 with
                 | (uu____3597,eff_label,uu____3599,uu____3600) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____3611 =
          let uu____3618 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____3652  ->
                    match uu____3652 with
                    | (uu____3665,uu____3666,flags1,uu____3668) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___337_3682  ->
                                match uu___337_3682 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____3683 -> false))))
             in
          if uu____3618
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____3611 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____3706 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____3708 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____3708
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____3746 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____3747 =
                     let uu____3752 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____3753 =
                       let uu____3754 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____3763 =
                         let uu____3774 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____3783 =
                           let uu____3794 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____3803 =
                             let uu____3814 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____3814]  in
                           uu____3794 :: uu____3803  in
                         uu____3774 :: uu____3783  in
                       uu____3754 :: uu____3763  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3752 uu____3753  in
                   uu____3747 FStar_Pervasives_Native.None uu____3746  in
                 let default_case =
                   let post_k =
                     let uu____3869 =
                       let uu____3878 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____3878]  in
                     let uu____3897 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____3869 uu____3897  in
                   let kwp =
                     let uu____3903 =
                       let uu____3912 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____3912]  in
                     let uu____3931 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____3903 uu____3931  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____3938 =
                       let uu____3939 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____3939]  in
                     let uu____3958 =
                       let uu____3961 =
                         let uu____3968 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____3968
                          in
                       let uu____3969 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____3961 uu____3969  in
                     FStar_Syntax_Util.abs uu____3938 uu____3958
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
                   let uu____3991 =
                     should_not_inline_whole_match ||
                       (let uu____3993 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____3993)
                      in
                   if uu____3991 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____4026  ->
                        fun celse  ->
                          match uu____4026 with
                          | (g,eff_label,uu____4042,cthen) ->
                              let uu____4054 =
                                let uu____4079 =
                                  let uu____4080 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____4080
                                   in
                                lift_and_destruct env uu____4079 celse  in
                              (match uu____4054 with
                               | ((md,uu____4082,uu____4083),(uu____4084,uu____4085,wp_then),
                                  (uu____4087,uu____4088,wp_else)) ->
                                   let uu____4108 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____4108 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____4122::[] -> comp
                 | uu____4162 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____4180 = destruct_comp comp1  in
                     (match uu____4180 with
                      | (uu____4187,uu____4188,wp) ->
                          let wp1 =
                            let uu____4193 =
                              let uu____4198 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____4199 =
                                let uu____4200 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____4209 =
                                  let uu____4220 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____4220]  in
                                uu____4200 :: uu____4209  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____4198
                                uu____4199
                               in
                            uu____4193 FStar_Pervasives_Native.None
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
          let uu____4287 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____4287 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____4302 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____4307 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____4302 uu____4307
              else
                (let uu____4315 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____4320 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____4315 uu____4320)
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
               let uu____4364 =
                 let uu____4365 = FStar_Syntax_Subst.compress t2  in
                 uu____4365.FStar_Syntax_Syntax.n  in
               match uu____4364 with
               | FStar_Syntax_Syntax.Tm_type uu____4368 -> true
               | uu____4369 -> false  in
             let uu____4370 =
               let uu____4371 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____4371.FStar_Syntax_Syntax.n  in
             match uu____4370 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____4379 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____4389 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____4389
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____4391 =
                     let uu____4392 =
                       let uu____4393 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____4393
                        in
                     (FStar_Pervasives_Native.None, uu____4392)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____4391
                    in
                 let e1 =
                   let uu____4399 =
                     let uu____4404 =
                       let uu____4405 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____4405]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4404  in
                   uu____4399 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____4432 -> (e, lc))
  
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
          (let uu____4466 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____4466
           then
             let uu____4467 = FStar_Syntax_Print.term_to_string e  in
             let uu____4468 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____4469 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____4467 uu____4468 uu____4469
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____4475 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____4475 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____4498 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____4520 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____4520, false)
             else
               (let uu____4526 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____4526, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____4537) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____4546 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____4546
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___356_4560 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___356_4560.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___356_4560.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___356_4560.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____4565 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____4565 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____4577 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let uu____4582 =
                        (let uu____4585 =
                           let uu____4586 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____4586
                             (FStar_TypeChecker_Env.norm_eff_name env)
                            in
                         FStar_All.pipe_right uu____4585
                           FStar_Syntax_Util.is_pure_or_ghost_effect)
                          ||
                          (let uu____4590 = FStar_Syntax_Util.eq_tm t res_t
                              in
                           uu____4590 = FStar_Syntax_Util.Equal)
                         in
                      if uu____4582
                      then
                        ((let uu____4592 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____4592
                          then
                            let uu____4593 =
                              FStar_Syntax_Print.lid_to_string
                                (FStar_Syntax_Util.comp_effect_name c)
                               in
                            let uu____4594 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____4595 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print3
                              "weaken_result_type::strengthen_trivial: Not inserting the return since either the comp c:%s is pure/ghost or res_t:%s is same as t:%s\n"
                              uu____4593 uu____4594 uu____4595
                          else ());
                         FStar_Syntax_Util.set_result_typ c t)
                      else
                        (let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (res_t.FStar_Syntax_Syntax.pos)) res_t
                            in
                         let cret =
                           let uu____4600 = FStar_Syntax_Syntax.bv_to_name x
                              in
                           return_value env (comp_univ_opt c) res_t
                             uu____4600
                            in
                         let lc1 =
                           let uu____4602 = FStar_Syntax_Util.lcomp_of_comp c
                              in
                           let uu____4603 =
                             let uu____4604 =
                               FStar_Syntax_Util.lcomp_of_comp cret  in
                             ((FStar_Pervasives_Native.Some x), uu____4604)
                              in
                           bind e.FStar_Syntax_Syntax.pos env
                             (FStar_Pervasives_Native.Some e) uu____4602
                             uu____4603
                            in
                         (let uu____4608 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____4608
                          then
                            let uu____4609 =
                              FStar_Syntax_Print.term_to_string e  in
                            let uu____4610 =
                              FStar_Syntax_Print.comp_to_string c  in
                            let uu____4611 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____4612 =
                              FStar_Syntax_Print.lcomp_to_string lc1  in
                            FStar_Util.print4
                              "weaken_result_type::strengthen_trivial: Inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                              uu____4609 uu____4610 uu____4611 uu____4612
                          else ());
                         (let uu____4614 = FStar_Syntax_Syntax.lcomp_comp lc1
                             in
                          FStar_Syntax_Util.set_result_typ uu____4614 t))
                       in
                    let lc1 =
                      FStar_Syntax_Syntax.mk_lcomp
                        lc.FStar_Syntax_Syntax.eff_name t
                        lc.FStar_Syntax_Syntax.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___357_4620 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___357_4620.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___357_4620.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___357_4620.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____4626 =
                      let uu____4627 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____4627
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____4630 =
                           let uu____4631 = FStar_Syntax_Subst.compress f1
                              in
                           uu____4631.FStar_Syntax_Syntax.n  in
                         match uu____4630 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____4634,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____4636;
                                           FStar_Syntax_Syntax.vars =
                                             uu____4637;_},uu____4638)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___358_4664 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___358_4664.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___358_4664.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___358_4664.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____4665 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____4668 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____4668
                               then
                                 let uu____4669 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____4670 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____4671 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____4672 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____4669 uu____4670 uu____4671
                                   uu____4672
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
                                   let uu____4681 =
                                     let uu____4686 =
                                       let uu____4687 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____4687]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____4686
                                      in
                                   uu____4681 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____4715 =
                                 let uu____4720 =
                                   FStar_All.pipe_left
                                     (fun _0_1  ->
                                        FStar_Pervasives_Native.Some _0_1)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____4737 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____4738 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____4739 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____4720
                                   uu____4737 e uu____4738 uu____4739
                                  in
                               match uu____4715 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___359_4743 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___359_4743.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___359_4743.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____4745 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____4745
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____4750 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____4750
                                     then
                                       let uu____4751 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____4751
                                     else ());
                                    c2))))
                       in
                    let flags1 =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___338_4761  ->
                              match uu___338_4761 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____4764 -> []))
                       in
                    let lc1 =
                      let uu____4766 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____4766 t flags1
                        strengthen
                       in
                    let g2 =
                      let uu___360_4768 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___360_4768.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___360_4768.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___360_4768.FStar_TypeChecker_Env.implicits)
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
        let uu____4803 =
          let uu____4806 =
            let uu____4811 =
              let uu____4812 =
                let uu____4821 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____4821  in
              [uu____4812]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4811  in
          uu____4806 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____4803  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____4846 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____4846
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____4862 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____4877 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____4893 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____4893
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____4907)::(ens,uu____4909)::uu____4910 ->
                    let uu____4953 =
                      let uu____4956 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____4956  in
                    let uu____4957 =
                      let uu____4958 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____4958  in
                    (uu____4953, uu____4957)
                | uu____4961 ->
                    let uu____4972 =
                      let uu____4977 =
                        let uu____4978 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____4978
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____4977)
                       in
                    FStar_Errors.raise_error uu____4972
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____4994)::uu____4995 ->
                    let uu____5022 =
                      let uu____5027 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____5027
                       in
                    (match uu____5022 with
                     | (us_r,uu____5059) ->
                         let uu____5060 =
                           let uu____5065 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____5065
                            in
                         (match uu____5060 with
                          | (us_e,uu____5097) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____5100 =
                                  let uu____5101 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5101
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5100
                                  us_r
                                 in
                              let as_ens =
                                let uu____5103 =
                                  let uu____5104 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5104
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5103
                                  us_e
                                 in
                              let req =
                                let uu____5108 =
                                  let uu____5113 =
                                    let uu____5114 =
                                      let uu____5125 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____5125]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5114
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____5113
                                   in
                                uu____5108 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____5167 =
                                  let uu____5172 =
                                    let uu____5173 =
                                      let uu____5184 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____5184]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5173
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____5172
                                   in
                                uu____5167 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____5223 =
                                let uu____5226 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____5226  in
                              let uu____5227 =
                                let uu____5228 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____5228  in
                              (uu____5223, uu____5227)))
                | uu____5231 -> failwith "Impossible"))
  
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
      (let uu____5263 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____5263
       then
         let uu____5264 = FStar_Syntax_Print.term_to_string tm  in
         let uu____5265 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____5264 uu____5265
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
        (let uu____5315 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____5315
         then
           let uu____5316 = FStar_Syntax_Print.term_to_string tm  in
           let uu____5317 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____5316
             uu____5317
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____5324 =
      let uu____5325 =
        let uu____5326 = FStar_Syntax_Subst.compress t  in
        uu____5326.FStar_Syntax_Syntax.n  in
      match uu____5325 with
      | FStar_Syntax_Syntax.Tm_app uu____5329 -> false
      | uu____5346 -> true  in
    if uu____5324
    then t
    else
      (let uu____5348 = FStar_Syntax_Util.head_and_args t  in
       match uu____5348 with
       | (head1,args) ->
           let uu____5391 =
             let uu____5392 =
               let uu____5393 = FStar_Syntax_Subst.compress head1  in
               uu____5393.FStar_Syntax_Syntax.n  in
             match uu____5392 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____5396 -> false  in
           if uu____5391
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____5426 ->
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
          ((let uu____5468 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____5468
            then
              let uu____5469 = FStar_Syntax_Print.term_to_string e  in
              let uu____5470 = FStar_Syntax_Print.term_to_string t  in
              let uu____5471 =
                let uu____5472 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____5472
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____5469 uu____5470 uu____5471
            else ());
           (let number_of_implicits t1 =
              let uu____5482 = FStar_Syntax_Util.arrow_formals t1  in
              match uu____5482 with
              | (formals,uu____5498) ->
                  let n_implicits =
                    let uu____5520 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____5598  ->
                              match uu____5598 with
                              | (uu____5605,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____5612 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____5612 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____5520 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____5738 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____5738 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____5762 =
                      let uu____5767 =
                        let uu____5768 = FStar_Util.string_of_int n_expected
                           in
                        let uu____5775 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____5776 = FStar_Util.string_of_int n_available
                           in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____5768 uu____5775 uu____5776
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____5767)
                       in
                    let uu____5783 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____5762 uu____5783
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___339_5806 =
              match uu___339_5806 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            match torig.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____5840 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____5840 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _0_2,uu____5955) when
                           _0_2 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____5998,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Implicit
                                      uu____6000))::rest)
                           ->
                           let t1 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6031 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t1
                              in
                           (match uu____6031 with
                            | (v1,uu____6071,g) ->
                                ((let uu____6086 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____6086
                                  then
                                    let uu____6087 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____6087
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____6094 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____6094 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____6187 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____6187))))
                       | (uu____6214,(x,FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t1 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6249 =
                             new_implicit_var
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t1
                              in
                           (match uu____6249 with
                            | (v1,uu____6289,g) ->
                                ((let uu____6304 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____6304
                                  then
                                    let uu____6305 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____6305
                                  else ());
                                 (let mark_meta_implicits tau1 g1 =
                                    let uu___361_6318 = g1  in
                                    let uu____6319 =
                                      FStar_List.map
                                        (fun imp  ->
                                           let uu___362_6325 = imp  in
                                           {
                                             FStar_TypeChecker_Env.imp_reason
                                               =
                                               (uu___362_6325.FStar_TypeChecker_Env.imp_reason);
                                             FStar_TypeChecker_Env.imp_uvar =
                                               (uu___362_6325.FStar_TypeChecker_Env.imp_uvar);
                                             FStar_TypeChecker_Env.imp_tm =
                                               (uu___362_6325.FStar_TypeChecker_Env.imp_tm);
                                             FStar_TypeChecker_Env.imp_range
                                               =
                                               (uu___362_6325.FStar_TypeChecker_Env.imp_range);
                                             FStar_TypeChecker_Env.imp_meta =
                                               (FStar_Pervasives_Native.Some
                                                  (env, tau1))
                                           })
                                        g1.FStar_TypeChecker_Env.implicits
                                       in
                                    {
                                      FStar_TypeChecker_Env.guard_f =
                                        (uu___361_6318.FStar_TypeChecker_Env.guard_f);
                                      FStar_TypeChecker_Env.deferred =
                                        (uu___361_6318.FStar_TypeChecker_Env.deferred);
                                      FStar_TypeChecker_Env.univ_ineqs =
                                        (uu___361_6318.FStar_TypeChecker_Env.univ_ineqs);
                                      FStar_TypeChecker_Env.implicits =
                                        uu____6319
                                    }  in
                                  let g1 = mark_meta_implicits tau g  in
                                  let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____6336 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____6336 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____6429 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____6429))))
                       | (uu____6456,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____6502 =
                       let uu____6529 = inst_n_binders t  in
                       aux [] uu____6529 bs1  in
                     (match uu____6502 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____6600) -> (e, torig, guard)
                           | (uu____6631,[]) when
                               let uu____6662 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____6662 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____6663 ->
                               let t1 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____6691 ->
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
            | uu____6704 -> (e, t, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____6714 =
      let uu____6717 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____6717
        (FStar_List.map
           (fun u  ->
              let uu____6727 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____6727 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____6714 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____6748 = FStar_Util.set_is_empty x  in
      if uu____6748
      then []
      else
        (let s =
           let uu____6763 =
             let uu____6766 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____6766  in
           FStar_All.pipe_right uu____6763 FStar_Util.set_elements  in
         (let uu____6782 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____6782
          then
            let uu____6783 =
              let uu____6784 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____6784  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____6783
          else ());
         (let r =
            let uu____6791 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____6791  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____6830 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____6830
                     then
                       let uu____6831 =
                         let uu____6832 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____6832
                          in
                       let uu____6833 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____6834 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____6831 uu____6833 uu____6834
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
        let uu____6860 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____6860 FStar_Util.set_elements  in
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
        | ([],uu____6898) -> generalized_univ_names
        | (uu____6905,[]) -> explicit_univ_names
        | uu____6912 ->
            let uu____6921 =
              let uu____6926 =
                let uu____6927 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____6927
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____6926)
               in
            FStar_Errors.raise_error uu____6921 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____6945 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____6945
       then
         let uu____6946 = FStar_Syntax_Print.term_to_string t  in
         let uu____6947 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____6946 uu____6947
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____6953 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____6953
        then
          let uu____6954 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____6954
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____6960 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____6960
         then
           let uu____6961 = FStar_Syntax_Print.term_to_string t  in
           let uu____6962 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____6961 uu____6962
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
        let uu____7040 =
          let uu____7041 =
            FStar_Util.for_all
              (fun uu____7054  ->
                 match uu____7054 with
                 | (uu____7063,uu____7064,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____7041  in
        if uu____7040
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____7112 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____7112
              then
                let uu____7113 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____7113
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____7117 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____7117
               then
                 let uu____7118 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7118
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____7133 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____7133 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____7167 =
             match uu____7167 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____7204 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____7204
                   then
                     let uu____7205 =
                       let uu____7206 =
                         let uu____7209 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____7209
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____7206
                         (FStar_String.concat ", ")
                        in
                     let uu____7252 =
                       let uu____7253 =
                         let uu____7256 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____7256
                           (FStar_List.map
                              (fun u  ->
                                 let uu____7267 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____7268 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____7267
                                   uu____7268))
                          in
                       FStar_All.pipe_right uu____7253
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____7205
                       uu____7252
                   else ());
                  (let univs2 =
                     let uu____7275 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____7287 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____7287) univs1
                       uu____7275
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____7294 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____7294
                    then
                      let uu____7295 =
                        let uu____7296 =
                          let uu____7299 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____7299
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____7296
                          (FStar_String.concat ", ")
                         in
                      let uu____7342 =
                        let uu____7343 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____7354 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____7355 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____7354
                                    uu____7355))
                           in
                        FStar_All.pipe_right uu____7343
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____7295
                        uu____7342
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____7369 =
             let uu____7386 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____7386  in
           match uu____7369 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____7476 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____7476
                 then ()
                 else
                   (let uu____7478 = lec_hd  in
                    match uu____7478 with
                    | (lb1,uu____7486,uu____7487) ->
                        let uu____7488 = lec2  in
                        (match uu____7488 with
                         | (lb2,uu____7496,uu____7497) ->
                             let msg =
                               let uu____7499 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____7500 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____7499 uu____7500
                                in
                             let uu____7501 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____7501))
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
                 let uu____7565 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____7565
                 then ()
                 else
                   (let uu____7567 = lec_hd  in
                    match uu____7567 with
                    | (lb1,uu____7575,uu____7576) ->
                        let uu____7577 = lec2  in
                        (match uu____7577 with
                         | (lb2,uu____7585,uu____7586) ->
                             let msg =
                               let uu____7588 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____7589 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____7588 uu____7589
                                in
                             let uu____7590 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____7590))
                  in
               let lecs1 =
                 let uu____7600 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____7653 = univs_and_uvars_of_lec this_lec  in
                        match uu____7653 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____7600 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____7754 = lec_hd  in
                   match uu____7754 with
                   | (lbname,e,c) ->
                       let uu____7764 =
                         let uu____7769 =
                           let uu____7770 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____7771 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____7772 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____7770 uu____7771 uu____7772
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____7769)
                          in
                       let uu____7773 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____7764 uu____7773
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____7794 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____7794 with
                         | FStar_Pervasives_Native.Some uu____7803 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____7810 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____7814 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____7814 with
                              | (bs,kres) ->
                                  ((let uu____7858 =
                                      let uu____7859 =
                                        let uu____7862 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine uu____7862
                                         in
                                      uu____7859.FStar_Syntax_Syntax.n  in
                                    match uu____7858 with
                                    | FStar_Syntax_Syntax.Tm_type uu____7863
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____7867 =
                                          let uu____7868 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____7868  in
                                        if uu____7867 then fail1 kres else ()
                                    | uu____7870 -> fail1 kres);
                                   (let a =
                                      let uu____7872 =
                                        let uu____7875 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_3  ->
                                             FStar_Pervasives_Native.Some
                                               _0_3) uu____7875
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____7872
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____7885 ->
                                          let uu____7894 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs uu____7894
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
                      (fun uu____8001  ->
                         match uu____8001 with
                         | (lbname,e,c) ->
                             let uu____8049 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____8124 ->
                                   let uu____8139 = (e, c)  in
                                   (match uu____8139 with
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
                                                (fun uu____8182  ->
                                                   match uu____8182 with
                                                   | (x,uu____8190) ->
                                                       let uu____8195 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____8195)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____8213 =
                                                let uu____8214 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____8214
                                                 in
                                              if uu____8213
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
                                          let uu____8220 =
                                            let uu____8221 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____8221.FStar_Syntax_Syntax.n
                                             in
                                          match uu____8220 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____8246 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____8246 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____8259 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____8263 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____8263, gen_tvars))
                                in
                             (match uu____8049 with
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
        (let uu____8417 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____8417
         then
           let uu____8418 =
             let uu____8419 =
               FStar_List.map
                 (fun uu____8432  ->
                    match uu____8432 with
                    | (lb,uu____8440,uu____8441) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____8419 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____8418
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____8462  ->
                match uu____8462 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____8491 = gen env is_rec lecs  in
           match uu____8491 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____8590  ->
                       match uu____8590 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____8652 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____8652
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____8698  ->
                           match uu____8698 with
                           | (l,us,e,c,gvs) ->
                               let uu____8732 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____8733 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____8734 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____8735 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____8736 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____8732 uu____8733 uu____8734 uu____8735
                                 uu____8736))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____8777  ->
                match uu____8777 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____8821 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____8821, t, c, gvs)) univnames_lecs
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
              (let uu____8878 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____8878 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____8884 = FStar_TypeChecker_Env.apply_guard f e  in
                   FStar_All.pipe_left
                     (fun _0_4  -> FStar_Pervasives_Native.Some _0_4)
                     uu____8884)
             in
          let is_var e1 =
            let uu____8893 =
              let uu____8894 = FStar_Syntax_Subst.compress e1  in
              uu____8894.FStar_Syntax_Syntax.n  in
            match uu____8893 with
            | FStar_Syntax_Syntax.Tm_name uu____8897 -> true
            | uu____8898 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___363_8918 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___363_8918.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___363_8918.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____8919 -> e2  in
          let env2 =
            let uu___364_8921 = env1  in
            let uu____8922 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___364_8921.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___364_8921.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___364_8921.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___364_8921.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___364_8921.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___364_8921.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___364_8921.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___364_8921.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___364_8921.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___364_8921.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___364_8921.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___364_8921.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___364_8921.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___364_8921.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___364_8921.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___364_8921.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___364_8921.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____8922;
              FStar_TypeChecker_Env.is_iface =
                (uu___364_8921.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___364_8921.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___364_8921.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___364_8921.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___364_8921.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___364_8921.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___364_8921.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___364_8921.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___364_8921.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___364_8921.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___364_8921.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___364_8921.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___364_8921.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___364_8921.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___364_8921.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___364_8921.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___364_8921.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___364_8921.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___364_8921.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___364_8921.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___364_8921.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___364_8921.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___364_8921.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___364_8921.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___364_8921.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____8923 = check1 env2 t1 t2  in
          match uu____8923 with
          | FStar_Pervasives_Native.None  ->
              let uu____8930 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____8935 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____8930 uu____8935
          | FStar_Pervasives_Native.Some g ->
              ((let uu____8942 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____8942
                then
                  let uu____8943 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____8943
                else ());
               (let uu____8945 = decorate e t2  in (uu____8945, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____8970 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____8970
         then
           let uu____8971 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____8971
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____8981 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____8981
         then
           let uu____8986 = discharge g1  in
           let uu____8987 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____8986, uu____8987)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____8994 =
                let uu____8995 =
                  let uu____8996 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____8996 FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____8995
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____8994
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____8998 = destruct_comp c1  in
            match uu____8998 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____9015 = FStar_TypeChecker_Env.get_range env  in
                  let uu____9016 =
                    let uu____9021 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____9022 =
                      let uu____9023 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____9032 =
                        let uu____9043 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____9043]  in
                      uu____9023 :: uu____9032  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____9021 uu____9022  in
                  uu____9016 FStar_Pervasives_Native.None uu____9015  in
                ((let uu____9079 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____9079
                  then
                    let uu____9080 = FStar_Syntax_Print.term_to_string vc  in
                    FStar_Util.print1 "top-level VC: %s\n" uu____9080
                  else ());
                 (let g2 =
                    let uu____9083 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____9083  in
                  let uu____9084 = discharge g2  in
                  let uu____9085 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____9084, uu____9085)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___340_9117 =
        match uu___340_9117 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____9127)::[] -> f fst1
        | uu____9152 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____9163 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____9163
          (fun _0_5  -> FStar_TypeChecker_Common.NonTrivial _0_5)
         in
      let op_or_e e =
        let uu____9174 =
          let uu____9175 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____9175  in
        FStar_All.pipe_right uu____9174
          (fun _0_6  -> FStar_TypeChecker_Common.NonTrivial _0_6)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_7  -> FStar_TypeChecker_Common.NonTrivial _0_7)
         in
      let op_or_t t =
        let uu____9194 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____9194
          (fun _0_8  -> FStar_TypeChecker_Common.NonTrivial _0_8)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_9  -> FStar_TypeChecker_Common.NonTrivial _0_9)
         in
      let short_op_ite uu___341_9208 =
        match uu___341_9208 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____9218)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____9245)::[] ->
            let uu____9286 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____9286
              (fun _0_10  -> FStar_TypeChecker_Common.NonTrivial _0_10)
        | uu____9287 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____9298 =
          let uu____9306 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____9306)  in
        let uu____9314 =
          let uu____9324 =
            let uu____9332 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____9332)  in
          let uu____9340 =
            let uu____9350 =
              let uu____9358 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____9358)  in
            let uu____9366 =
              let uu____9376 =
                let uu____9384 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____9384)  in
              let uu____9392 =
                let uu____9402 =
                  let uu____9410 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____9410)  in
                [uu____9402; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____9376 :: uu____9392  in
            uu____9350 :: uu____9366  in
          uu____9324 :: uu____9340  in
        uu____9298 :: uu____9314  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____9472 =
            FStar_Util.find_map table
              (fun uu____9487  ->
                 match uu____9487 with
                 | (x,mk1) ->
                     let uu____9504 = FStar_Ident.lid_equals x lid  in
                     if uu____9504
                     then
                       let uu____9507 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____9507
                     else FStar_Pervasives_Native.None)
             in
          (match uu____9472 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____9510 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____9516 =
      let uu____9517 = FStar_Syntax_Util.un_uinst l  in
      uu____9517.FStar_Syntax_Syntax.n  in
    match uu____9516 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____9521 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____9555)::uu____9556 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____9575 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____9584,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____9585))::uu____9586 -> bs
      | uu____9603 ->
          let uu____9604 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____9604 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____9608 =
                 let uu____9609 = FStar_Syntax_Subst.compress t  in
                 uu____9609.FStar_Syntax_Syntax.n  in
               (match uu____9608 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____9613) ->
                    let uu____9634 =
                      FStar_Util.prefix_until
                        (fun uu___342_9674  ->
                           match uu___342_9674 with
                           | (uu____9681,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9682)) ->
                               false
                           | uu____9685 -> true) bs'
                       in
                    (match uu____9634 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____9720,uu____9721) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____9793,uu____9794) ->
                         let uu____9867 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____9885  ->
                                   match uu____9885 with
                                   | (x,uu____9893) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____9867
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____9940  ->
                                     match uu____9940 with
                                     | (x,i) ->
                                         let uu____9959 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____9959, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____9969 -> bs))
  
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
            let uu____9997 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____9997
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
          let uu____10024 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____10024
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
        (let uu____10059 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____10059
         then
           ((let uu____10061 = FStar_Ident.text_of_lid lident  in
             d uu____10061);
            (let uu____10062 = FStar_Ident.text_of_lid lident  in
             let uu____10063 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____10062 uu____10063))
         else ());
        (let fv =
           let uu____10066 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____10066
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
         let uu____10076 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___365_10078 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___365_10078.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___365_10078.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___365_10078.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___365_10078.FStar_Syntax_Syntax.sigattrs)
           }), uu____10076))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___343_10094 =
        match uu___343_10094 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10095 -> false  in
      let reducibility uu___344_10101 =
        match uu___344_10101 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____10102 -> false  in
      let assumption uu___345_10108 =
        match uu___345_10108 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____10109 -> false  in
      let reification uu___346_10115 =
        match uu___346_10115 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____10116 -> true
        | uu____10117 -> false  in
      let inferred uu___347_10123 =
        match uu___347_10123 with
        | FStar_Syntax_Syntax.Discriminator uu____10124 -> true
        | FStar_Syntax_Syntax.Projector uu____10125 -> true
        | FStar_Syntax_Syntax.RecordType uu____10130 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____10139 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____10148 -> false  in
      let has_eq uu___348_10154 =
        match uu___348_10154 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____10155 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____10219 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10224 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____10234 =
        let uu____10235 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___349_10239  ->
                  match uu___349_10239 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____10240 -> false))
           in
        FStar_All.pipe_right uu____10235 Prims.op_Negation  in
      if uu____10234
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____10255 =
            let uu____10260 =
              let uu____10261 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____10261 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____10260)  in
          FStar_Errors.raise_error uu____10255 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____10273 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____10277 =
            let uu____10278 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____10278  in
          if uu____10277 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____10283),uu____10284) ->
              ((let uu____10294 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____10294
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____10298 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____10298
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____10304 ->
              let uu____10313 =
                let uu____10314 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          ((((x = FStar_Syntax_Syntax.Abstract) ||
                               (x = FStar_Syntax_Syntax.NoExtract))
                              || (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____10314  in
              if uu____10313 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____10320 ->
              let uu____10327 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____10327 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____10331 ->
              let uu____10338 =
                let uu____10339 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____10339  in
              if uu____10338 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____10345 ->
              let uu____10346 =
                let uu____10347 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____10347  in
              if uu____10346 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10353 ->
              let uu____10354 =
                let uu____10355 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____10355  in
              if uu____10354 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10361 ->
              let uu____10374 =
                let uu____10375 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____10375  in
              if uu____10374 then err'1 () else ()
          | uu____10381 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____10415 =
          let uu____10416 = FStar_Syntax_Subst.compress t1  in
          uu____10416.FStar_Syntax_Syntax.n  in
        match uu____10415 with
        | FStar_Syntax_Syntax.Tm_type uu____10419 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____10422 =
                 let uu____10427 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____10427
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____10422
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____10445 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____10445
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____10462 =
                                 let uu____10463 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____10463.FStar_Syntax_Syntax.n  in
                               match uu____10462 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____10467 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____10468 ->
            let uu____10483 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____10483 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____10515 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____10515
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____10517;
               FStar_Syntax_Syntax.index = uu____10518;
               FStar_Syntax_Syntax.sort = t2;_},uu____10520)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____10528,uu____10529) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____10571::[]) ->
            let uu____10610 =
              let uu____10611 = FStar_Syntax_Util.un_uinst head1  in
              uu____10611.FStar_Syntax_Syntax.n  in
            (match uu____10610 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____10615 -> false)
        | uu____10616 -> false
      
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
        (let uu____10624 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____10624
         then
           let uu____10625 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____10625
         else ());
        res
       in aux g t
  