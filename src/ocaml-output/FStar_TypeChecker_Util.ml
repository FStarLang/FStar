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
    Prims.bool ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun solve_deferred  ->
      fun xs  ->
        fun g  ->
          let uu____91 = (FStar_Options.eager_subtyping ()) || solve_deferred
             in
          if uu____91
          then
            let uu____94 =
              FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
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
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____215)
                       solve_now;
                     FStar_Util.print_string " ...DEFERRED THE REST:\n";
                     FStar_List.iter
                       (fun uu____230  ->
                          match uu____230 with
                          | (s,p) ->
                              let uu____240 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____240) defer;
                     FStar_Util.print_string "END\n")
                  else ());
                 (let g1 =
                    FStar_TypeChecker_Rel.solve_deferred_constraints env
                      (let uu___49_248 = g  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___49_248.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred = solve_now;
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___49_248.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits =
                           (uu___49_248.FStar_TypeChecker_Common.implicits)
                       })
                     in
                  let g2 =
                    let uu___52_250 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___52_250.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred = defer;
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___52_250.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits =
                        (uu___52_250.FStar_TypeChecker_Common.implicits)
                    }  in
                  g2))
          else g
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____267 =
        let uu____269 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____269  in
      if uu____267
      then
        let us =
          let uu____274 =
            let uu____278 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____278
             in
          FStar_All.pipe_right uu____274 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____297 =
            let uu____303 =
              let uu____305 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____305
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____303)  in
          FStar_Errors.log_issue r uu____297);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____328  ->
      match uu____328 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____339;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____341;
          FStar_Syntax_Syntax.lbpos = uu____342;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____377 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____377 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____415) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____422) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____477) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____513 = FStar_Options.ml_ish ()  in
                                if uu____513
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____535 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____535
                            then
                              let uu____538 = FStar_Range.string_of_range r
                                 in
                              let uu____540 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____538 uu____540
                            else ());
                           FStar_Util.Inl t2)
                      | uu____545 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____547 = aux e1  in
                      match uu____547 with
                      | FStar_Util.Inr c ->
                          let uu____553 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____553
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____558 =
                               let uu____564 =
                                 let uu____566 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____566
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____564)
                                in
                             FStar_Errors.raise_error uu____558 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____575 ->
               let uu____576 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____576 with
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
    let pat_as_arg uu____640 =
      match uu____640 with
      | (p,i) ->
          let uu____660 = decorated_pattern_as_term p  in
          (match uu____660 with
           | (vars,te) ->
               let uu____683 =
                 let uu____688 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____688)  in
               (vars, uu____683))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____702 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____702)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____706 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____706)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____710 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____710)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____733 =
          let uu____752 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____752 FStar_List.unzip  in
        (match uu____733 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____890 =
               let uu____891 =
                 let uu____892 =
                   let uu____909 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____909, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____892  in
               mk1 uu____891  in
             (vars1, uu____890))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____948,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____958,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____972 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc  ->
    let uu____987 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp  in
    FStar_All.pipe_right uu____987
      (fun uu____1015  ->
         match uu____1015 with | (c,g) -> ((comp_univ_opt c), g))
  
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
        let uu____1078 =
          FStar_All.pipe_right
            (let uu___169_1080 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___169_1080.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___169_1080.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___169_1080.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___169_1080.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____1078
          (lift.FStar_TypeChecker_Env.mlift_wp env)
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1101 =
          let uu____1108 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1109 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1108 uu____1109  in
        match uu____1101 with | (m,uu____1111,uu____1112) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1129 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1129
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
            let uu____1184 =
              FStar_TypeChecker_Env.join env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____1184 with
            | (m,lift1,lift2) ->
                let uu____1202 = lift_comp env c11 lift1  in
                (match uu____1202 with
                 | (c12,g1) ->
                     let uu____1217 =
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
                          let uu____1256 = lift_comp env_x c21 lift2  in
                          match uu____1256 with
                          | (c22,g2) ->
                              let uu____1267 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____1267))
                        in
                     (match uu____1217 with
                      | (c22,g2) ->
                          let uu____1290 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (m, c12, c22, uu____1290)))
  
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
            let uu____1351 =
              let uu____1352 =
                let uu____1363 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1363]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1352;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1351
  
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
          let uu____1447 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1447
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1459 =
      let uu____1460 = FStar_Syntax_Subst.compress t  in
      uu____1460.FStar_Syntax_Syntax.n  in
    match uu____1459 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1464 -> true
    | uu____1480 -> false
  
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
              let uu____1550 =
                let uu____1552 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1552  in
              if uu____1550
              then f
              else (let uu____1559 = reason1 ()  in label uu____1559 r f)
  
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
            let uu___246_1580 = g  in
            let uu____1581 =
              let uu____1582 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1582  in
            {
              FStar_TypeChecker_Common.guard_f = uu____1581;
              FStar_TypeChecker_Common.deferred =
                (uu___246_1580.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___246_1580.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___246_1580.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1603 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1603
        then c
        else
          (let uu____1608 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1608
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____1650 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____1650 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____1678 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____1678]  in
                       let us =
                         let uu____1700 =
                           let uu____1703 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____1703]  in
                         u_res :: uu____1700  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____1709 =
                         let uu____1714 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____1715 =
                           let uu____1716 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____1725 =
                             let uu____1736 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____1745 =
                               let uu____1756 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____1756]  in
                             uu____1736 :: uu____1745  in
                           uu____1716 :: uu____1725  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1714 uu____1715
                          in
                       uu____1709 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1798 = destruct_wp_comp c1  in
              match uu____1798 with
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
                let uu____1838 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____1838
                  (close_guard_implicits env false bs)))
  
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
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_1901  ->
            match uu___0_1901 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1904 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____1929 =
            let uu____1932 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____1932 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____1929
            (fun c  ->
               (let uu____1988 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____1988) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____1992 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____1992)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2003 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2003 with
                | (head1,uu____2020) ->
                    let uu____2041 =
                      let uu____2042 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2042.FStar_Syntax_Syntax.n  in
                    (match uu____2041 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2047 =
                           let uu____2049 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2049
                            in
                         Prims.op_Negation uu____2047
                     | uu____2050 -> true)))
              &&
              (let uu____2053 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2053)
  
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
            let uu____2081 =
              let uu____2083 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2083  in
            if uu____2081
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2090 = FStar_Syntax_Util.is_unit t  in
               if uu____2090
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
                    let uu____2099 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2099
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2104 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2104 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let ret_wp =
                             FStar_All.pipe_right m
                               FStar_Syntax_Util.get_return_vc_combinator
                              in
                           let uu____2115 =
                             let uu____2116 =
                               let uu____2121 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m ret_wp
                                  in
                               let uu____2122 =
                                 let uu____2123 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2132 =
                                   let uu____2143 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2143]  in
                                 uu____2123 :: uu____2132  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2121
                                 uu____2122
                                in
                             uu____2116 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2115)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2177 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2177
           then
             let uu____2182 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2184 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2186 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2182 uu____2184 uu____2186
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
                (let uu____2244 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____2244
                 then
                   let uu____2249 =
                     let uu____2251 = FStar_Syntax_Syntax.mk_Comp ct1  in
                     FStar_Syntax_Print.comp_to_string uu____2251  in
                   let uu____2252 =
                     let uu____2254 = FStar_Syntax_Syntax.mk_Comp ct2  in
                     FStar_Syntax_Print.comp_to_string uu____2254  in
                   FStar_Util.print2 "Binding c1:%s and c2:%s {\n" uu____2249
                     uu____2252
                 else ());
                (let ed = FStar_TypeChecker_Env.get_effect_decl env m  in
                 let uu____2259 =
                   let uu____2270 =
                     FStar_List.hd ct1.FStar_Syntax_Syntax.comp_univs  in
                   let uu____2271 =
                     FStar_List.map FStar_Pervasives_Native.fst
                       ct1.FStar_Syntax_Syntax.effect_args
                      in
                   (uu____2270, (ct1.FStar_Syntax_Syntax.result_typ),
                     uu____2271)
                    in
                 match uu____2259 with
                 | (u1,t1,is1) ->
                     let uu____2305 =
                       let uu____2316 =
                         FStar_List.hd ct2.FStar_Syntax_Syntax.comp_univs  in
                       let uu____2317 =
                         FStar_List.map FStar_Pervasives_Native.fst
                           ct2.FStar_Syntax_Syntax.effect_args
                          in
                       (uu____2316, (ct2.FStar_Syntax_Syntax.result_typ),
                         uu____2317)
                        in
                     (match uu____2305 with
                      | (u2,t2,is2) ->
                          let uu____2351 =
                            let uu____2356 =
                              FStar_All.pipe_right ed
                                FStar_Syntax_Util.get_bind_vc_combinator
                               in
                            FStar_TypeChecker_Env.inst_tscheme_with
                              uu____2356 [u1; u2]
                             in
                          (match uu____2351 with
                           | (uu____2361,bind_t) ->
                               let bind_t_shape_error s =
                                 let uu____2376 =
                                   let uu____2378 =
                                     FStar_Syntax_Print.term_to_string bind_t
                                      in
                                   FStar_Util.format2
                                     "bind %s does not have proper shape (reason:%s)"
                                     uu____2378 s
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____2376)
                                  in
                               let uu____2382 =
                                 let uu____2427 =
                                   let uu____2428 =
                                     FStar_Syntax_Subst.compress bind_t  in
                                   uu____2428.FStar_Syntax_Syntax.n  in
                                 match uu____2427 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____2504 =
                                       FStar_Syntax_Subst.open_comp bs c  in
                                     (match uu____2504 with
                                      | (a_b::b_b::bs1,c1) ->
                                          let uu____2589 =
                                            let uu____2616 =
                                              FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   (Prims.of_int (2))) bs1
                                               in
                                            FStar_All.pipe_right uu____2616
                                              (fun uu____2701  ->
                                                 match uu____2701 with
                                                 | (l1,l2) ->
                                                     let uu____2782 =
                                                       FStar_List.hd l2  in
                                                     let uu____2795 =
                                                       let uu____2802 =
                                                         FStar_List.tl l2  in
                                                       FStar_List.hd
                                                         uu____2802
                                                        in
                                                     (l1, uu____2782,
                                                       uu____2795))
                                             in
                                          (match uu____2589 with
                                           | (rest_bs,f_b,g_b) ->
                                               let uu____2930 =
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                   c1
                                                  in
                                               (a_b, b_b, rest_bs, f_b, g_b,
                                                 uu____2930)))
                                 | uu____2963 ->
                                     let uu____2964 =
                                       bind_t_shape_error
                                         "Either not an arrow or not enough binders"
                                        in
                                     FStar_Errors.raise_error uu____2964 r1
                                  in
                               (match uu____2382 with
                                | (a_b,b_b,rest_bs,f_b,g_b,bind_ct) ->
                                    let uu____3089 =
                                      let uu____3096 =
                                        let uu____3097 =
                                          let uu____3098 =
                                            let uu____3105 =
                                              FStar_All.pipe_right a_b
                                                FStar_Pervasives_Native.fst
                                               in
                                            (uu____3105, t1)  in
                                          FStar_Syntax_Syntax.NT uu____3098
                                           in
                                        let uu____3116 =
                                          let uu____3119 =
                                            let uu____3120 =
                                              let uu____3127 =
                                                FStar_All.pipe_right b_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____3127, t2)  in
                                            FStar_Syntax_Syntax.NT uu____3120
                                             in
                                          [uu____3119]  in
                                        uu____3097 :: uu____3116  in
                                      FStar_TypeChecker_Env.uvars_for_binders
                                        env rest_bs uu____3096
                                        (fun b1  ->
                                           let uu____3142 =
                                             FStar_Syntax_Print.binder_to_string
                                               b1
                                              in
                                           let uu____3144 =
                                             FStar_Range.string_of_range r1
                                              in
                                           FStar_Util.format3
                                             "implicit var for binder %s of %s:bind at %s"
                                             uu____3142
                                             (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             uu____3144) r1
                                       in
                                    (match uu____3089 with
                                     | (rest_bs_uvars,g_uvars) ->
                                         let subst1 =
                                           FStar_List.map2
                                             (fun b1  ->
                                                fun t  ->
                                                  let uu____3181 =
                                                    let uu____3188 =
                                                      FStar_All.pipe_right b1
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    (uu____3188, t)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3181) (a_b :: b_b
                                             :: rest_bs) (t1 :: t2 ::
                                             rest_bs_uvars)
                                            in
                                         let f_guard =
                                           let f_sort_is =
                                             let uu____3215 =
                                               let uu____3216 =
                                                 let uu____3219 =
                                                   let uu____3220 =
                                                     FStar_All.pipe_right f_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3220.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3219
                                                  in
                                               uu____3216.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3215 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____3231,uu____3232::is)
                                                 ->
                                                 let uu____3274 =
                                                   FStar_All.pipe_right is
                                                     (FStar_List.map
                                                        FStar_Pervasives_Native.fst)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3274
                                                   (FStar_List.map
                                                      (FStar_Syntax_Subst.subst
                                                         subst1))
                                             | uu____3307 ->
                                                 let uu____3308 =
                                                   bind_t_shape_error
                                                     "f's type is not a repr type"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3308 r1
                                              in
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun i1  ->
                                                  fun f_i1  ->
                                                    let uu____3324 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env i1 f_i1
                                                       in
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g uu____3324)
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
                                             let uu____3343 =
                                               let uu____3344 =
                                                 let uu____3347 =
                                                   let uu____3348 =
                                                     FStar_All.pipe_right g_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3348.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3347
                                                  in
                                               uu____3344.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3343 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs,c) ->
                                                 let uu____3381 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c
                                                    in
                                                 (match uu____3381 with
                                                  | (bs1,c1) ->
                                                      let bs_subst =
                                                        let uu____3391 =
                                                          let uu____3398 =
                                                            let uu____3399 =
                                                              FStar_List.hd
                                                                bs1
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3399
                                                              FStar_Pervasives_Native.fst
                                                             in
                                                          let uu____3420 =
                                                            let uu____3423 =
                                                              FStar_All.pipe_right
                                                                x_a
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3423
                                                              FStar_Syntax_Syntax.bv_to_name
                                                             in
                                                          (uu____3398,
                                                            uu____3420)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____3391
                                                         in
                                                      let c2 =
                                                        FStar_Syntax_Subst.subst_comp
                                                          [bs_subst] c1
                                                         in
                                                      let uu____3437 =
                                                        let uu____3438 =
                                                          FStar_Syntax_Subst.compress
                                                            (FStar_Syntax_Util.comp_result
                                                               c2)
                                                           in
                                                        uu____3438.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____3437 with
                                                       | FStar_Syntax_Syntax.Tm_app
                                                           (uu____3443,uu____3444::is)
                                                           ->
                                                           let uu____3486 =
                                                             FStar_All.pipe_right
                                                               is
                                                               (FStar_List.map
                                                                  FStar_Pervasives_Native.fst)
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____3486
                                                             (FStar_List.map
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1))
                                                       | uu____3519 ->
                                                           let uu____3520 =
                                                             bind_t_shape_error
                                                               "g's type is not a repr type"
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____3520 r1))
                                             | uu____3529 ->
                                                 let uu____3530 =
                                                   bind_t_shape_error
                                                     "g's type is not an arrow"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3530 r1
                                              in
                                           let env_g =
                                             FStar_TypeChecker_Env.push_binders
                                               env [x_a]
                                              in
                                           let uu____3552 =
                                             FStar_List.fold_left2
                                               (fun g  ->
                                                  fun i1  ->
                                                    fun g_i1  ->
                                                      let uu____3560 =
                                                        FStar_TypeChecker_Rel.teq
                                                          env_g i1 g_i1
                                                         in
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g uu____3560)
                                               FStar_TypeChecker_Env.trivial_guard
                                               is2 g_sort_is
                                              in
                                           FStar_All.pipe_right uu____3552
                                             (FStar_TypeChecker_Env.close_guard
                                                env [x_a])
                                            in
                                         let is =
                                           let uu____3576 =
                                             let uu____3577 =
                                               FStar_Syntax_Subst.compress
                                                 bind_ct.FStar_Syntax_Syntax.result_typ
                                                in
                                             uu____3577.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3576 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____3582,uu____3583::is) ->
                                               let uu____3625 =
                                                 FStar_All.pipe_right is
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3625
                                                 (FStar_List.map
                                                    (FStar_Syntax_Subst.subst
                                                       subst1))
                                           | uu____3658 ->
                                               let uu____3659 =
                                                 bind_t_shape_error
                                                   "return type is not a repr type"
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____3659 r1
                                            in
                                         let c =
                                           let uu____3669 =
                                             let uu____3670 =
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
                                                 = uu____3670;
                                               FStar_Syntax_Syntax.flags =
                                                 flags
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____3669
                                            in
                                         ((let uu____3690 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffects")
                                              in
                                           if uu____3690
                                           then
                                             let uu____3695 =
                                               FStar_Syntax_Print.comp_to_string
                                                 c
                                                in
                                             FStar_Util.print1
                                               "} c after bind: %s\n"
                                               uu____3695
                                           else ());
                                          (let uu____3700 =
                                             FStar_TypeChecker_Env.conj_guards
                                               [g_uvars; f_guard; g_guard]
                                              in
                                           (c, uu____3700))))))))
  
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
                let uu____3745 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____3771 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____3771 with
                  | (a,kwp) ->
                      let uu____3802 = destruct_wp_comp ct1  in
                      let uu____3809 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____3802, uu____3809)
                   in
                match uu____3745 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____3862 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____3862]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____3882 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3882]
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
                      let uu____3929 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____3938 =
                        let uu____3949 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____3958 =
                          let uu____3969 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____3978 =
                            let uu____3989 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____3998 =
                              let uu____4009 =
                                let uu____4018 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____4018  in
                              [uu____4009]  in
                            uu____3989 :: uu____3998  in
                          uu____3969 :: uu____3978  in
                        uu____3949 :: uu____3958  in
                      uu____3929 :: uu____3938  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____4071 =
                        let uu____4076 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4076 wp_args  in
                      uu____4071 FStar_Pervasives_Native.None
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
              let uu____4124 = lift_comps env c1 c2 b true  in
              match uu____4124 with
              | (m,c11,c21,g_lift) ->
                  let uu____4142 =
                    let uu____4147 = FStar_Syntax_Util.comp_to_comp_typ c11
                       in
                    let uu____4148 = FStar_Syntax_Util.comp_to_comp_typ c21
                       in
                    (uu____4147, uu____4148)  in
                  (match uu____4142 with
                   | (ct1,ct2) ->
                       let uu____4155 =
                         let uu____4160 =
                           FStar_TypeChecker_Env.is_layered_effect env m  in
                         if uu____4160
                         then mk_layered_bind env m ct1 b ct2 flags r1
                         else
                           (let uu____4169 =
                              mk_non_layered_bind env m ct1 b ct2 flags r1
                               in
                            (uu____4169, FStar_TypeChecker_Env.trivial_guard))
                          in
                       (match uu____4155 with
                        | (c,g_bind) ->
                            let uu____4176 =
                              FStar_TypeChecker_Env.conj_guard g_lift g_bind
                               in
                            (c, uu____4176)))
  
let (bind_pure_wp_with :
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
          let pure_c =
            let uu____4212 =
              let uu____4213 =
                let uu____4224 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____4224]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4213;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4212  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____4269 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4275  ->
              match uu___1_4275 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4278 -> false))
       in
    if uu____4269
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4290  ->
              match uu___2_4290 with
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
        let uu____4318 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4318
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____4329 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____4329  in
           let pure_assume_wp1 =
             let uu____4334 = FStar_TypeChecker_Env.get_range env  in
             let uu____4335 =
               let uu____4340 =
                 let uu____4341 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____4341]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4340  in
             uu____4335 FStar_Pervasives_Native.None uu____4334  in
           let uu____4374 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____4374)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4402 =
          let uu____4403 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____4403 with
          | (c,g_c) ->
              let uu____4414 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4414
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____4428 = weaken_comp env c f1  in
                     (match uu____4428 with
                      | (c1,g_w) ->
                          let uu____4439 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____4439)))
           in
        let uu____4440 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____4440 weaken
  
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
                 let uu____4497 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____4497  in
               let pure_assert_wp1 =
                 let uu____4502 =
                   let uu____4507 =
                     let uu____4508 =
                       let uu____4517 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____4517
                        in
                     [uu____4508]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____4507
                    in
                 uu____4502 FStar_Pervasives_Native.None r  in
               bind_pure_wp_with env pure_assert_wp1 c flags)
  
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
            let uu____4587 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____4587
            then (lc, g0)
            else
              (let flags =
                 let uu____4599 =
                   let uu____4607 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____4607
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4599 with
                 | (maybe_trivial_post,flags) ->
                     let uu____4637 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_4645  ->
                               match uu___3_4645 with
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
                               | uu____4648 -> []))
                        in
                     FStar_List.append flags uu____4637
                  in
               let strengthen uu____4658 =
                 let uu____4659 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____4659 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____4678 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____4678 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____4685 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4685
                              then
                                let uu____4689 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____4691 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____4689 uu____4691
                              else ());
                             (let uu____4696 =
                                strengthen_comp env reason c f flags  in
                              match uu____4696 with
                              | (c1,g_s) ->
                                  let uu____4707 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____4707))))
                  in
               let uu____4708 =
                 let uu____4709 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____4709
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____4708,
                 (let uu___562_4711 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___562_4711.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___562_4711.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___562_4711.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_4720  ->
            match uu___4_4720 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4724 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____4753 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4753
          then e
          else
            (let uu____4760 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4763 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4763)
                in
             if uu____4760
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
  
let (maybe_capture_unit_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
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
              ({ FStar_Syntax_Syntax.ppname = uu____4823;
                 FStar_Syntax_Syntax.index = uu____4824;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____4826;
                     FStar_Syntax_Syntax.vars = uu____4827;_};_},uu____4828)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              let uu____4836 =
                let uu____4838 =
                  let uu____4839 =
                    FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name
                     in
                  FStar_All.pipe_right uu____4839
                    (FStar_TypeChecker_Env.norm_eff_name env)
                   in
                FStar_All.pipe_right uu____4838
                  (FStar_TypeChecker_Env.is_layered_effect env)
                 in
              if uu____4836
              then
                let uu____4848 = t1.FStar_Syntax_Syntax.n  in
                (match uu____4848 with
                 | FStar_Syntax_Syntax.Tm_refine (b,phi) ->
                     let uu____4859 =
                       FStar_Syntax_Subst.open_term
                         [(b, FStar_Pervasives_Native.None)] phi
                        in
                     (match uu____4859 with
                      | (b1::[],phi1) ->
                          let phi2 =
                            let uu____4903 =
                              let uu____4906 =
                                let uu____4907 =
                                  let uu____4914 =
                                    FStar_All.pipe_right b1
                                      FStar_Pervasives_Native.fst
                                     in
                                  (uu____4914,
                                    FStar_Syntax_Syntax.unit_const)
                                   in
                                FStar_Syntax_Syntax.NT uu____4907  in
                              [uu____4906]  in
                            FStar_Syntax_Subst.subst uu____4903 phi1  in
                          weaken_comp env c phi2))
              else
                (let uu____4927 = close_wp_comp env [x] c  in
                 (uu____4927, FStar_TypeChecker_Env.trivial_guard))
          | uu____4928 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____4956  ->
            match uu____4956 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4976 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____4976 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____4989 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____4989
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____4999 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____4999
                       then
                         let uu____5004 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____5004
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5011 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____5011
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5020 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____5020
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5027 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5027
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____5043 =
                  let uu____5044 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5044
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____5052 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____5052, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____5055 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____5055 with
                     | (c1,g_c1) ->
                         let uu____5066 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____5066 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____5086  ->
                                    let uu____5087 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____5089 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____5094 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____5087 uu____5089 uu____5094);
                               (let aux uu____5112 =
                                  let uu____5113 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____5113
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5144
                                        ->
                                        let uu____5145 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5145
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5177 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5177
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____5224 =
                                  let aux_with_trivial_guard uu____5254 =
                                    let uu____5255 = aux ()  in
                                    match uu____5255 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c,
                                            FStar_TypeChecker_Env.trivial_guard,
                                            reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____5313 =
                                    let uu____5315 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____5315  in
                                  if uu____5313
                                  then
                                    let uu____5331 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____5331
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           FStar_TypeChecker_Env.trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5358 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5358))
                                  else
                                    (let uu____5375 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____5375
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___667_5421 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___667_5421.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___667_5421.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____5422 =
                                           maybe_capture_unit_refinement env
                                             x1.FStar_Syntax_Syntax.sort x1 c
                                            in
                                         match uu____5422 with
                                         | (c3,g_c) ->
                                             FStar_Util.Inl (c3, g_c, reason)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____5480 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____5480
                                             (close1 x "c1 Tot")
                                       | (uu____5496,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____5521,uu____5522) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____5537 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____5537
                                        then
                                          let uu____5552 =
                                            let uu____5560 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____5560,
                                              FStar_TypeChecker_Env.trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____5552
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____5573 = try_simplify ()  in
                                match uu____5573 with
                                | FStar_Util.Inl (c,g_c,reason) ->
                                    (debug1
                                       (fun uu____5608  ->
                                          let uu____5609 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____5609);
                                     (let uu____5612 =
                                        let uu____5613 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c1 g_c2
                                           in
                                        FStar_TypeChecker_Env.conj_guard g_c
                                          uu____5613
                                         in
                                      (c, uu____5612)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____5627  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____5653 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____5653 with
                                        | (c,g_bind) ->
                                            let uu____5664 =
                                              let uu____5665 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5665 g_bind
                                               in
                                            (c, uu____5664)
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
                                        let uu____5692 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5692 with
                                        | (m,uu____5704,lift2) ->
                                            let uu____5706 =
                                              lift_comp env c22 lift2  in
                                            (match uu____5706 with
                                             | (c23,g2) ->
                                                 let uu____5717 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____5717 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____5733 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5733
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____5743 =
                                                          let uu____5748 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____5749 =
                                                            let uu____5750 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5759 =
                                                              let uu____5770
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5770]
                                                               in
                                                            uu____5750 ::
                                                              uu____5759
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5748
                                                            uu____5749
                                                           in
                                                        uu____5743
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5803 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____5803 with
                                                       | (c,g_s) ->
                                                           let uu____5818 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____5818))))
                                         in
                                      let uu____5819 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5835 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____5835, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____5819 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____5851 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____5851
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____5860 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____5860
                                             then
                                               (debug1
                                                  (fun uu____5874  ->
                                                     let uu____5875 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____5877 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____5875 uu____5877);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____5885 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____5888 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____5888)
                                                   in
                                                if uu____5885
                                                then
                                                  let e1' =
                                                    let uu____5913 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____5913
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____5925  ->
                                                        let uu____5926 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____5928 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____5926
                                                          uu____5928);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____5943  ->
                                                        let uu____5944 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5946 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____5944
                                                          uu____5946);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____5953 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____5953
                                                       in
                                                    let uu____5954 =
                                                      let uu____5959 =
                                                        let uu____5960 =
                                                          let uu____5961 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____5961]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____5960
                                                         in
                                                      weaken_comp uu____5959
                                                        c21 x_eq_e
                                                       in
                                                    match uu____5954 with
                                                    | (c22,g_w) ->
                                                        let uu____5986 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____5986
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____5997 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____5997))))))
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
      | uu____6014 -> g2
  
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
            (let uu____6038 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6038)
           in
        let flags =
          if should_return1
          then
            let uu____6046 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6046
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6064 =
          let uu____6065 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6065 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6078 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6078
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6086 =
                  let uu____6088 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6088  in
                (if uu____6086
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___786_6097 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___786_6097.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___786_6097.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___786_6097.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6098 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6098, g_c)
                 else
                   (let uu____6101 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6101, g_c)))
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
                   let uu____6112 =
                     let uu____6113 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6113
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6112
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6116 =
                   let uu____6121 =
                     let uu____6122 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6122
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6121  in
                 match uu____6116 with
                 | (bind_c,g_bind) ->
                     let uu____6131 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6132 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6131, uu____6132))
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
            fun uu____6168  ->
              match uu____6168 with
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
                    let uu____6180 =
                      ((let uu____6184 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6184) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6180
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6202 =
        let uu____6203 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6203  in
      FStar_Syntax_Syntax.fvar uu____6202 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (mk_layered_conjunction :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.comp_typ ->
                FStar_Range.range ->
                  (FStar_Syntax_Syntax.comp *
                    FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                fun r  ->
                  let uu____6253 =
                    let uu____6258 =
                      let uu____6259 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____6259 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____6258 [u_a]
                     in
                  match uu____6253 with
                  | (uu____6270,conjunction) ->
                      let uu____6272 =
                        let uu____6281 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____6296 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____6281, uu____6296)  in
                      (match uu____6272 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____6342 =
                               let uu____6344 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____6344 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____6342)
                              in
                           let uu____6348 =
                             let uu____6393 =
                               let uu____6394 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____6394.FStar_Syntax_Syntax.n  in
                             match uu____6393 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____6443) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____6475 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____6475 with
                                  | (a_b::bs1,body1) ->
                                      let uu____6547 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____6547 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____6695 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____6695)))
                             | uu____6728 ->
                                 let uu____6729 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____6729 r
                              in
                           (match uu____6348 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____6854 =
                                  let uu____6861 =
                                    let uu____6862 =
                                      let uu____6863 =
                                        let uu____6870 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____6870, a)  in
                                      FStar_Syntax_Syntax.NT uu____6863  in
                                    [uu____6862]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____6861
                                    (fun b  ->
                                       let uu____6886 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____6888 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____6890 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____6886 uu____6888 uu____6890) r
                                   in
                                (match uu____6854 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____6928 =
                                                let uu____6935 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____6935, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____6928) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____6974 =
                                           let uu____6975 =
                                             let uu____6978 =
                                               let uu____6979 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____6979.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____6978
                                              in
                                           uu____6975.FStar_Syntax_Syntax.n
                                            in
                                         match uu____6974 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____6990,uu____6991::is) ->
                                             let uu____7033 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7033
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7066 ->
                                             let uu____7067 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7067 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____7083 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7083)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____7088 =
                                           let uu____7089 =
                                             let uu____7092 =
                                               let uu____7093 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7093.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7092
                                              in
                                           uu____7089.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7088 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7104,uu____7105::is) ->
                                             let uu____7147 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7147
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7180 ->
                                             let uu____7181 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7181 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____7197 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7197)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____7202 =
                                         let uu____7203 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____7203.FStar_Syntax_Syntax.n  in
                                       match uu____7202 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7208,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____7263 ->
                                           let uu____7264 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____7264 r
                                        in
                                     let uu____7273 =
                                       let uu____7274 =
                                         let uu____7275 =
                                           FStar_All.pipe_right is
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.as_arg)
                                            in
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             [u_a];
                                           FStar_Syntax_Syntax.effect_name =
                                             (ed.FStar_Syntax_Syntax.mname);
                                           FStar_Syntax_Syntax.result_typ = a;
                                           FStar_Syntax_Syntax.effect_args =
                                             uu____7275;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____7274
                                        in
                                     let uu____7298 =
                                       let uu____7299 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____7299 g_guard
                                        in
                                     (uu____7273, uu____7298))))
  
let (mk_non_layered_conjunction :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.comp_typ ->
                FStar_Range.range ->
                  (FStar_Syntax_Syntax.comp *
                    FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                fun uu____7344  ->
                  let if_then_else1 =
                    let uu____7350 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____7350 FStar_Util.must  in
                  let uu____7357 = destruct_wp_comp ct1  in
                  match uu____7357 with
                  | (uu____7368,uu____7369,wp_t) ->
                      let uu____7371 = destruct_wp_comp ct2  in
                      (match uu____7371 with
                       | (uu____7382,uu____7383,wp_e) ->
                           let wp =
                             let uu____7388 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____7389 =
                               let uu____7394 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____7395 =
                                 let uu____7396 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____7405 =
                                   let uu____7416 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____7425 =
                                     let uu____7436 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____7445 =
                                       let uu____7456 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____7456]  in
                                     uu____7436 :: uu____7445  in
                                   uu____7416 :: uu____7425  in
                                 uu____7396 :: uu____7405  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____7394
                                 uu____7395
                                in
                             uu____7389 FStar_Pervasives_Native.None
                               uu____7388
                              in
                           let uu____7505 = mk_comp ed u_a a wp []  in
                           (uu____7505, FStar_TypeChecker_Env.trivial_guard))
  
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
               fun uu____7575  ->
                 match uu____7575 with
                 | (uu____7589,eff_label,uu____7591,uu____7592) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____7605 =
          let uu____7613 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____7651  ->
                    match uu____7651 with
                    | (uu____7666,uu____7667,flags,uu____7669) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_7686  ->
                                match uu___5_7686 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____7689 -> false))))
             in
          if uu____7613
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____7605 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____7726 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____7728 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____7728
              then
                let uu____7735 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____7735, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____7742 =
                       let uu____7751 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7751]  in
                     let uu____7770 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7742 uu____7770  in
                   let kwp =
                     let uu____7776 =
                       let uu____7785 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7785]  in
                     let uu____7804 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7776 uu____7804  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7811 =
                       let uu____7812 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7812]  in
                     let uu____7831 =
                       let uu____7834 =
                         let uu____7841 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7841
                          in
                       let uu____7842 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7834 uu____7842  in
                     FStar_Syntax_Util.abs uu____7811 uu____7831
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
                   let uu____7866 =
                     should_not_inline_whole_match ||
                       (let uu____7869 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7869)
                      in
                   if uu____7866 then cthen true else cthen false  in
                 let uu____7876 =
                   FStar_List.fold_right
                     (fun uu____7929  ->
                        fun uu____7930  ->
                          match (uu____7929, uu____7930) with
                          | ((g,eff_label,uu____7984,cthen),(uu____7986,celse,g_comp))
                              ->
                              let uu____8027 =
                                let uu____8032 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____8032
                                 in
                              (match uu____8027 with
                               | (cthen1,gthen) ->
                                   let uu____8043 =
                                     let uu____8052 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____8052 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____8075 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____8076 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____8075, uu____8076, g_lift)
                                      in
                                   (match uu____8043 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          let uu____8126 =
                                            FStar_All.pipe_right md
                                              FStar_Syntax_Util.is_layered
                                             in
                                          if uu____8126
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____8160 =
                                          let uu____8165 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____8165
                                           in
                                        (match uu____8160 with
                                         | (c,g_conjunction) ->
                                             let uu____8176 =
                                               let uu____8177 =
                                                 let uu____8178 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____8178 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____8177 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____8176)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____7876 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____8212::[] -> (comp, g_comp)
                      | uu____8255 ->
                          let uu____8272 =
                            let uu____8274 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            FStar_All.pipe_right uu____8274
                              FStar_Syntax_Util.is_layered
                             in
                          if uu____8272
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
                             let uu____8287 = destruct_wp_comp comp1  in
                             match uu____8287 with
                             | (uu____8298,uu____8299,wp) ->
                                 let ite_wp =
                                   let uu____8302 =
                                     FStar_All.pipe_right md1
                                       FStar_Syntax_Util.get_wp_ite_combinator
                                      in
                                   FStar_All.pipe_right uu____8302
                                     FStar_Util.must
                                    in
                                 let wp1 =
                                   let uu____8312 =
                                     let uu____8317 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_res_t] env md1 ite_wp
                                        in
                                     let uu____8318 =
                                       let uu____8319 =
                                         FStar_Syntax_Syntax.as_arg res_t  in
                                       let uu____8328 =
                                         let uu____8339 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [uu____8339]  in
                                       uu____8319 :: uu____8328  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____8317
                                       uu____8318
                                      in
                                   uu____8312 FStar_Pervasives_Native.None
                                     wp.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____8372 =
                                   mk_comp md1 u_res_t res_t wp1
                                     bind_cases_flags
                                    in
                                 (uu____8372, g_comp))))
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
          let uu____8406 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____8406 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____8422 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____8428 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____8422 uu____8428
              else
                (let uu____8437 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____8443 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____8437 uu____8443)
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
          let uu____8468 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____8468
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____8471 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____8471
        then u_res
        else
          (let is_total =
             let uu____8478 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____8478
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____8489 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____8489 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8492 =
                    let uu____8498 =
                      let uu____8500 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____8500
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____8498)
                     in
                  FStar_Errors.raise_error uu____8492
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
      let uu____8524 = destruct_wp_comp ct  in
      match uu____8524 with
      | (u_t,t,wp) ->
          let vc =
            let uu____8543 = FStar_TypeChecker_Env.get_range env  in
            let uu____8544 =
              let uu____8549 =
                let uu____8550 =
                  let uu____8551 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____8551 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____8550
                 in
              let uu____8558 =
                let uu____8559 = FStar_Syntax_Syntax.as_arg t  in
                let uu____8568 =
                  let uu____8579 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____8579]  in
                uu____8559 :: uu____8568  in
              FStar_Syntax_Syntax.mk_Tm_app uu____8549 uu____8558  in
            uu____8544 FStar_Pervasives_Native.None uu____8543  in
          let uu____8612 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____8612)
  
let (coerce_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.universes ->
              FStar_Syntax_Syntax.args ->
                (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp) ->
                  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun ty  ->
          fun f  ->
            fun us  ->
              fun eargs  ->
                fun mkcomp  ->
                  let uu____8667 = FStar_TypeChecker_Env.try_lookup_lid env f
                     in
                  match uu____8667 with
                  | FStar_Pervasives_Native.Some uu____8682 ->
                      ((let uu____8700 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____8700
                        then
                          let uu____8704 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____8704
                        else ());
                       (let coercion =
                          let uu____8710 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____8710
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____8717 =
                            let uu____8718 =
                              let uu____8719 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____8719
                               in
                            (FStar_Pervasives_Native.None, uu____8718)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____8717
                           in
                        let e1 =
                          let uu____8725 =
                            let uu____8730 =
                              let uu____8731 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____8731]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____8730
                             in
                          uu____8725 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8765 =
                          let uu____8771 =
                            let uu____8773 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____8773
                             in
                          (FStar_Errors.Warning_CoercionNotFound, uu____8771)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____8765);
                       (e, lc))
  
let (maybe_coerce_lc :
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
          let should_coerce =
            (((let uu____8810 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____8810) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc)
          else
            (let is_t_term t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8827 =
                 let uu____8828 = FStar_Syntax_Subst.compress t2  in
                 uu____8828.FStar_Syntax_Syntax.n  in
               match uu____8827 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____8833 -> false  in
             let is_t_term_view t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8843 =
                 let uu____8844 = FStar_Syntax_Subst.compress t2  in
                 uu____8844.FStar_Syntax_Syntax.n  in
               match uu____8843 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____8849 -> false  in
             let is_type1 t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8859 =
                 let uu____8860 = FStar_Syntax_Subst.compress t2  in
                 uu____8860.FStar_Syntax_Syntax.n  in
               match uu____8859 with
               | FStar_Syntax_Syntax.Tm_type uu____8864 -> true
               | uu____8866 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____8869 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____8869 with
             | (head1,args) ->
                 ((let uu____8917 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____8917
                   then
                     let uu____8921 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____8923 = FStar_Syntax_Print.term_to_string e  in
                     let uu____8925 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____8927 = FStar_Syntax_Print.term_to_string t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____8921 uu____8923 uu____8925 uu____8927
                   else ());
                  (let is_erased env1 t1 t2 =
                     let uu____8949 = FStar_Syntax_Util.head_and_args t2  in
                     match uu____8949 with
                     | (head2,args1) ->
                         let uu____8993 =
                           let uu____9008 =
                             let uu____9009 =
                               FStar_Syntax_Util.un_uinst head2  in
                             uu____9009.FStar_Syntax_Syntax.n  in
                           (uu____9008, args1)  in
                         (match uu____8993 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(x,FStar_Pervasives_Native.None )::[]) ->
                              (FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.erased_lid)
                                && (FStar_Syntax_Util.term_eq x t1)
                          | uu____9057 -> false)
                      in
                   let uu____9073 =
                     let uu____9088 =
                       let uu____9089 = FStar_Syntax_Util.un_uinst head1  in
                       uu____9089.FStar_Syntax_Syntax.n  in
                     (uu____9088, args)  in
                   match uu____9073 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 t)
                       ->
                       coerce_with env e lc FStar_Syntax_Util.ktype0
                         FStar_Parser_Const.b2t_lid [] []
                         FStar_Syntax_Syntax.mk_Total
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view t)
                       ->
                       coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                         FStar_Parser_Const.inspect [] []
                         FStar_Syntax_Syntax.mk_Tac
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term t)
                       ->
                       coerce_with env e lc FStar_Syntax_Syntax.t_term
                         FStar_Parser_Const.pack [] []
                         FStar_Syntax_Syntax.mk_Tac
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term t)
                       ->
                       coerce_with env e lc FStar_Syntax_Syntax.t_term
                         FStar_Parser_Const.binder_to_term [] []
                         FStar_Syntax_Syntax.mk_Tac
                   | uu____9214 when is_erased env t res_typ ->
                       let uu____9229 =
                         let uu____9230 =
                           env.FStar_TypeChecker_Env.universe_of env t  in
                         [uu____9230]  in
                       let uu____9231 =
                         let uu____9232 = FStar_Syntax_Syntax.iarg t  in
                         [uu____9232]  in
                       coerce_with env e lc t FStar_Parser_Const.reveal
                         uu____9229 uu____9231 FStar_Syntax_Syntax.mk_GTotal
                   | uu____9257 when is_erased env res_typ t ->
                       let uu____9272 =
                         let uu____9273 =
                           env.FStar_TypeChecker_Env.universe_of env res_typ
                            in
                         [uu____9273]  in
                       let uu____9274 =
                         let uu____9275 = FStar_Syntax_Syntax.iarg res_typ
                            in
                         [uu____9275]  in
                       coerce_with env e lc t FStar_Parser_Const.hide
                         uu____9272 uu____9274 FStar_Syntax_Syntax.mk_Total
                   | uu____9300 -> (e, lc))))
  
let (coerce_views :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let rt = lc.FStar_TypeChecker_Common.res_typ  in
        let rt1 = FStar_Syntax_Util.unrefine rt  in
        let uu____9345 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____9345 with
        | (hd1,args) ->
            let uu____9394 =
              let uu____9409 =
                let uu____9410 = FStar_Syntax_Subst.compress hd1  in
                uu____9410.FStar_Syntax_Syntax.n  in
              (uu____9409, args)  in
            (match uu____9394 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____9448 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Total
                    in
                 FStar_All.pipe_left
                   (fun _9475  -> FStar_Pervasives_Native.Some _9475)
                   uu____9448
             | uu____9476 -> FStar_Pervasives_Native.None)
  
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
          (let uu____9529 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____9529
           then
             let uu____9532 = FStar_Syntax_Print.term_to_string e  in
             let uu____9534 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____9536 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____9532 uu____9534 uu____9536
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____9546 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____9546 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____9571 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____9597 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____9597, false)
             else
               (let uu____9607 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____9607, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____9620) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____9632 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____9632
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1141_9648 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1141_9648.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1141_9648.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1141_9648.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____9655 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____9655 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____9671 =
                      let uu____9672 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____9672 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____9692 =
                            let uu____9694 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____9694 = FStar_Syntax_Util.Equal  in
                          if uu____9692
                          then
                            ((let uu____9701 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____9701
                              then
                                let uu____9705 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____9707 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____9705 uu____9707
                              else ());
                             (let uu____9712 = set_result_typ1 c  in
                              (uu____9712, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____9719 ->
                                   true
                               | uu____9727 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____9736 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____9736
                                  in
                               let lc1 =
                                 let uu____9738 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____9739 =
                                   let uu____9740 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____9740)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____9738 uu____9739
                                  in
                               ((let uu____9744 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____9744
                                 then
                                   let uu____9748 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____9750 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____9752 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____9754 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____9748 uu____9750 uu____9752
                                     uu____9754
                                 else ());
                                (let uu____9759 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____9759 with
                                 | (c1,g_lc) ->
                                     let uu____9770 = set_result_typ1 c1  in
                                     let uu____9771 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____9770, uu____9771)))
                             else
                               ((let uu____9775 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____9775
                                 then
                                   let uu____9779 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____9781 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____9779 uu____9781
                                 else ());
                                (let uu____9786 = set_result_typ1 c  in
                                 (uu____9786, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1178_9790 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1178_9790.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1178_9790.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1178_9790.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____9800 =
                      let uu____9801 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____9801
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____9811 =
                           let uu____9812 = FStar_Syntax_Subst.compress f1
                              in
                           uu____9812.FStar_Syntax_Syntax.n  in
                         match uu____9811 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____9819,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____9821;
                                           FStar_Syntax_Syntax.vars =
                                             uu____9822;_},uu____9823)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1194_9849 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1194_9849.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1194_9849.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1194_9849.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____9850 ->
                             let uu____9851 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____9851 with
                              | (c,g_c) ->
                                  ((let uu____9863 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____9863
                                    then
                                      let uu____9867 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____9869 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____9871 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____9873 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____9867 uu____9869 uu____9871
                                        uu____9873
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
                                        let uu____9886 =
                                          let uu____9891 =
                                            let uu____9892 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____9892]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____9891
                                           in
                                        uu____9886
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____9919 =
                                      let uu____9924 =
                                        FStar_All.pipe_left
                                          (fun _9945  ->
                                             FStar_Pervasives_Native.Some
                                               _9945)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____9946 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____9947 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____9948 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____9924
                                        uu____9946 e uu____9947 uu____9948
                                       in
                                    match uu____9919 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1212_9956 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1212_9956.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1212_9956.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____9958 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____9958
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____9961 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____9961 with
                                         | (c2,g_lc) ->
                                             ((let uu____9973 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____9973
                                               then
                                                 let uu____9977 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____9977
                                               else ());
                                              (let uu____9982 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____9982))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_9991  ->
                              match uu___6_9991 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____9994 -> []))
                       in
                    let lc1 =
                      let uu____9996 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____9996 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1228_9998 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1228_9998.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1228_9998.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1228_9998.FStar_TypeChecker_Common.implicits)
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
        let uu____10034 =
          let uu____10037 =
            let uu____10042 =
              let uu____10043 =
                let uu____10052 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____10052  in
              [uu____10043]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____10042  in
          uu____10037 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____10034  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____10075 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____10075
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____10094 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____10110 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____10127 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____10127
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____10143)::(ens,uu____10145)::uu____10146 ->
                    let uu____10189 =
                      let uu____10192 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____10192  in
                    let uu____10193 =
                      let uu____10194 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____10194  in
                    (uu____10189, uu____10193)
                | uu____10197 ->
                    let uu____10208 =
                      let uu____10214 =
                        let uu____10216 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____10216
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____10214)
                       in
                    FStar_Errors.raise_error uu____10208
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____10236)::uu____10237 ->
                    let uu____10264 =
                      let uu____10269 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____10269
                       in
                    (match uu____10264 with
                     | (us_r,uu____10301) ->
                         let uu____10302 =
                           let uu____10307 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____10307
                            in
                         (match uu____10302 with
                          | (us_e,uu____10339) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____10342 =
                                  let uu____10343 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10343
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10342
                                  us_r
                                 in
                              let as_ens =
                                let uu____10345 =
                                  let uu____10346 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10346
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10345
                                  us_e
                                 in
                              let req =
                                let uu____10350 =
                                  let uu____10355 =
                                    let uu____10356 =
                                      let uu____10367 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10367]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10356
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____10355
                                   in
                                uu____10350 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____10407 =
                                  let uu____10412 =
                                    let uu____10413 =
                                      let uu____10424 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10424]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10413
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____10412
                                   in
                                uu____10407 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____10461 =
                                let uu____10464 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____10464  in
                              let uu____10465 =
                                let uu____10466 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____10466  in
                              (uu____10461, uu____10465)))
                | uu____10469 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun steps  ->
      fun t  ->
        let tm = FStar_Syntax_Util.mk_reify t  in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            (FStar_List.append
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.EraseUniverses;
               FStar_TypeChecker_Env.AllowUnboundUniverses;
               FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
               steps) env tm
           in
        (let uu____10508 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____10508
         then
           let uu____10513 = FStar_Syntax_Print.term_to_string tm  in
           let uu____10515 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____10513
             uu____10515
         else ());
        tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun steps  ->
      fun head1  ->
        fun arg  ->
          let tm =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
              FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
             in
          let tm' =
            FStar_TypeChecker_Normalize.normalize
              (FStar_List.append
                 [FStar_TypeChecker_Env.Beta;
                 FStar_TypeChecker_Env.Reify;
                 FStar_TypeChecker_Env.Eager_unfolding;
                 FStar_TypeChecker_Env.EraseUniverses;
                 FStar_TypeChecker_Env.AllowUnboundUniverses;
                 FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
                 steps) env tm
             in
          (let uu____10574 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____10574
           then
             let uu____10579 = FStar_Syntax_Print.term_to_string tm  in
             let uu____10581 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____10579
               uu____10581
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____10592 =
      let uu____10594 =
        let uu____10595 = FStar_Syntax_Subst.compress t  in
        uu____10595.FStar_Syntax_Syntax.n  in
      match uu____10594 with
      | FStar_Syntax_Syntax.Tm_app uu____10599 -> false
      | uu____10617 -> true  in
    if uu____10592
    then t
    else
      (let uu____10622 = FStar_Syntax_Util.head_and_args t  in
       match uu____10622 with
       | (head1,args) ->
           let uu____10665 =
             let uu____10667 =
               let uu____10668 = FStar_Syntax_Subst.compress head1  in
               uu____10668.FStar_Syntax_Syntax.n  in
             match uu____10667 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____10673 -> false  in
           if uu____10665
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____10705 ->
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
          ((let uu____10752 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____10752
            then
              let uu____10755 = FStar_Syntax_Print.term_to_string e  in
              let uu____10757 = FStar_Syntax_Print.term_to_string t  in
              let uu____10759 =
                let uu____10761 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____10761
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____10755 uu____10757 uu____10759
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____10774 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____10774 with
              | (formals,uu____10790) ->
                  let n_implicits =
                    let uu____10812 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____10890  ->
                              match uu____10890 with
                              | (uu____10898,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____10905 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____10905 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____10812 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____11030 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____11030 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____11044 =
                      let uu____11050 =
                        let uu____11052 = FStar_Util.string_of_int n_expected
                           in
                        let uu____11054 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____11056 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____11052 uu____11054 uu____11056
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____11050)
                       in
                    let uu____11060 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____11044 uu____11060
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_11078 =
              match uu___7_11078 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____11121 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____11121 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _11252,uu____11239)
                           when _11252 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____11285,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____11287))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____11321 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____11321 with
                            | (v1,uu____11362,g) ->
                                ((let uu____11377 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____11377
                                  then
                                    let uu____11380 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____11380
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____11390 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____11390 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____11483 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____11483))))
                       | (uu____11510,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____11547 =
                             let uu____11560 =
                               let uu____11567 =
                                 let uu____11572 = FStar_Dyn.mkdyn env  in
                                 (uu____11572, tau)  in
                               FStar_Pervasives_Native.Some uu____11567  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____11560
                              in
                           (match uu____11547 with
                            | (v1,uu____11605,g) ->
                                ((let uu____11620 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____11620
                                  then
                                    let uu____11623 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____11623
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____11633 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____11633 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____11726 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____11726))))
                       | (uu____11753,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____11801 =
                       let uu____11828 = inst_n_binders t1  in
                       aux [] uu____11828 bs1  in
                     (match uu____11801 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____11900) -> (e, torig, guard)
                           | (uu____11931,[]) when
                               let uu____11962 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____11962 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11964 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____11992 ->
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
            | uu____12005 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____12017 =
      let uu____12021 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____12021
        (FStar_List.map
           (fun u  ->
              let uu____12033 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____12033 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____12017 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____12061 = FStar_Util.set_is_empty x  in
      if uu____12061
      then []
      else
        (let s =
           let uu____12079 =
             let uu____12082 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____12082  in
           FStar_All.pipe_right uu____12079 FStar_Util.set_elements  in
         (let uu____12098 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____12098
          then
            let uu____12103 =
              let uu____12105 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____12105  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____12103
          else ());
         (let r =
            let uu____12114 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____12114  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____12153 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____12153
                     then
                       let uu____12158 =
                         let uu____12160 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____12160
                          in
                       let uu____12164 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____12166 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____12158 uu____12164 uu____12166
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
        let uu____12196 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____12196 FStar_Util.set_elements  in
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
        | ([],uu____12235) -> generalized_univ_names
        | (uu____12242,[]) -> explicit_univ_names
        | uu____12249 ->
            let uu____12258 =
              let uu____12264 =
                let uu____12266 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____12266
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____12264)
               in
            FStar_Errors.raise_error uu____12258 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____12288 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____12288
       then
         let uu____12293 = FStar_Syntax_Print.term_to_string t  in
         let uu____12295 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____12293 uu____12295
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____12304 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____12304
        then
          let uu____12309 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____12309
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____12318 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____12318
         then
           let uu____12323 = FStar_Syntax_Print.term_to_string t  in
           let uu____12325 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____12323 uu____12325
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
        let uu____12409 =
          let uu____12411 =
            FStar_Util.for_all
              (fun uu____12425  ->
                 match uu____12425 with
                 | (uu____12435,uu____12436,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____12411  in
        if uu____12409
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____12488 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____12488
              then
                let uu____12491 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____12491
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____12498 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____12498
               then
                 let uu____12501 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____12501
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____12519 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____12519 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____12553 =
             match uu____12553 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____12590 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____12590
                   then
                     let uu____12595 =
                       let uu____12597 =
                         let uu____12601 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____12601
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____12597
                         (FStar_String.concat ", ")
                        in
                     let uu____12649 =
                       let uu____12651 =
                         let uu____12655 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____12655
                           (FStar_List.map
                              (fun u  ->
                                 let uu____12668 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____12670 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____12668
                                   uu____12670))
                          in
                       FStar_All.pipe_right uu____12651
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____12595
                       uu____12649
                   else ());
                  (let univs2 =
                     let uu____12684 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____12696 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____12696) univs1
                       uu____12684
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____12703 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____12703
                    then
                      let uu____12708 =
                        let uu____12710 =
                          let uu____12714 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____12714
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____12710
                          (FStar_String.concat ", ")
                         in
                      let uu____12762 =
                        let uu____12764 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____12778 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____12780 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____12778
                                    uu____12780))
                           in
                        FStar_All.pipe_right uu____12764
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____12708 uu____12762
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____12801 =
             let uu____12818 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____12818  in
           match uu____12801 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____12908 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____12908
                 then ()
                 else
                   (let uu____12913 = lec_hd  in
                    match uu____12913 with
                    | (lb1,uu____12921,uu____12922) ->
                        let uu____12923 = lec2  in
                        (match uu____12923 with
                         | (lb2,uu____12931,uu____12932) ->
                             let msg =
                               let uu____12935 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____12937 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____12935 uu____12937
                                in
                             let uu____12940 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____12940))
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
                 let uu____13008 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____13008
                 then ()
                 else
                   (let uu____13013 = lec_hd  in
                    match uu____13013 with
                    | (lb1,uu____13021,uu____13022) ->
                        let uu____13023 = lec2  in
                        (match uu____13023 with
                         | (lb2,uu____13031,uu____13032) ->
                             let msg =
                               let uu____13035 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____13037 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____13035 uu____13037
                                in
                             let uu____13040 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____13040))
                  in
               let lecs1 =
                 let uu____13051 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____13104 = univs_and_uvars_of_lec this_lec  in
                        match uu____13104 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____13051 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____13209 = lec_hd  in
                   match uu____13209 with
                   | (lbname,e,c) ->
                       let uu____13219 =
                         let uu____13225 =
                           let uu____13227 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____13229 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____13231 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____13227 uu____13229 uu____13231
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____13225)
                          in
                       let uu____13235 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____13219 uu____13235
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____13254 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____13254 with
                         | FStar_Pervasives_Native.Some uu____13263 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____13271 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____13275 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____13275 with
                              | (bs,kres) ->
                                  ((let uu____13319 =
                                      let uu____13320 =
                                        let uu____13323 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____13323
                                         in
                                      uu____13320.FStar_Syntax_Syntax.n  in
                                    match uu____13319 with
                                    | FStar_Syntax_Syntax.Tm_type uu____13324
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____13328 =
                                          let uu____13330 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____13330  in
                                        if uu____13328
                                        then fail1 kres
                                        else ()
                                    | uu____13335 -> fail1 kres);
                                   (let a =
                                      let uu____13337 =
                                        let uu____13340 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _13343  ->
                                             FStar_Pervasives_Native.Some
                                               _13343) uu____13340
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____13337
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____13351 ->
                                          let uu____13360 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____13360
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
                      (fun uu____13463  ->
                         match uu____13463 with
                         | (lbname,e,c) ->
                             let uu____13509 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____13570 ->
                                   let uu____13583 = (e, c)  in
                                   (match uu____13583 with
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
                                                (fun uu____13623  ->
                                                   match uu____13623 with
                                                   | (x,uu____13629) ->
                                                       let uu____13630 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____13630)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____13648 =
                                                let uu____13650 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____13650
                                                 in
                                              if uu____13648
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
                                          let uu____13659 =
                                            let uu____13660 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____13660.FStar_Syntax_Syntax.n
                                             in
                                          match uu____13659 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____13685 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____13685 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____13696 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____13700 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____13700, gen_tvars))
                                in
                             (match uu____13509 with
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
        (let uu____13847 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____13847
         then
           let uu____13850 =
             let uu____13852 =
               FStar_List.map
                 (fun uu____13867  ->
                    match uu____13867 with
                    | (lb,uu____13876,uu____13877) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____13852 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____13850
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____13903  ->
                match uu____13903 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____13932 = gen env is_rec lecs  in
           match uu____13932 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____14031  ->
                       match uu____14031 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____14093 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____14093
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____14141  ->
                           match uu____14141 with
                           | (l,us,e,c,gvs) ->
                               let uu____14175 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____14177 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____14179 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____14181 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____14183 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____14175 uu____14177 uu____14179
                                 uu____14181 uu____14183))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____14228  ->
                match uu____14228 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____14272 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____14272, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
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
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t1 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
            else
              (let uu____14337 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____14337 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____14343 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _14346  -> FStar_Pervasives_Native.Some _14346)
                     uu____14343)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1681_14366 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1681_14366.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1681_14366.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____14367 -> e2  in
          let uu____14368 = maybe_coerce_lc env1 e lc t2  in
          match uu____14368 with
          | (e1,lc1) ->
              let uu____14381 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____14381 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14390 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____14396 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____14390 uu____14396
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____14405 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____14405
                     then
                       let uu____14410 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____14410
                     else ());
                    (let uu____14416 = decorate e1 t2  in
                     (uu____14416, lc1, g))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____14444 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____14444
         then
           let uu____14447 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____14447
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____14461 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____14461 with
         | (c,g_c) ->
             let uu____14473 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____14473
             then
               let uu____14481 =
                 let uu____14483 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____14483  in
               (uu____14481, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____14491 =
                    let uu____14492 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____14492
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____14491
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____14493 = check_trivial_precondition env c1  in
                match uu____14493 with
                | (ct,vc,g_pre) ->
                    ((let uu____14509 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____14509
                      then
                        let uu____14514 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____14514
                      else ());
                     (let uu____14519 =
                        let uu____14521 =
                          let uu____14522 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____14522  in
                        discharge uu____14521  in
                      let uu____14523 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____14519, uu____14523)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_14557 =
        match uu___8_14557 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____14567)::[] -> f fst1
        | uu____14592 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____14604 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____14604
          (fun _14605  -> FStar_TypeChecker_Common.NonTrivial _14605)
         in
      let op_or_e e =
        let uu____14616 =
          let uu____14617 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____14617  in
        FStar_All.pipe_right uu____14616
          (fun _14620  -> FStar_TypeChecker_Common.NonTrivial _14620)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _14627  -> FStar_TypeChecker_Common.NonTrivial _14627)
         in
      let op_or_t t =
        let uu____14638 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____14638
          (fun _14641  -> FStar_TypeChecker_Common.NonTrivial _14641)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _14648  -> FStar_TypeChecker_Common.NonTrivial _14648)
         in
      let short_op_ite uu___9_14654 =
        match uu___9_14654 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____14664)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____14691)::[] ->
            let uu____14732 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____14732
              (fun _14733  -> FStar_TypeChecker_Common.NonTrivial _14733)
        | uu____14734 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____14746 =
          let uu____14754 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____14754)  in
        let uu____14762 =
          let uu____14772 =
            let uu____14780 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____14780)  in
          let uu____14788 =
            let uu____14798 =
              let uu____14806 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____14806)  in
            let uu____14814 =
              let uu____14824 =
                let uu____14832 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____14832)  in
              let uu____14840 =
                let uu____14850 =
                  let uu____14858 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____14858)  in
                [uu____14850; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____14824 :: uu____14840  in
            uu____14798 :: uu____14814  in
          uu____14772 :: uu____14788  in
        uu____14746 :: uu____14762  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____14920 =
            FStar_Util.find_map table
              (fun uu____14935  ->
                 match uu____14935 with
                 | (x,mk1) ->
                     let uu____14952 = FStar_Ident.lid_equals x lid  in
                     if uu____14952
                     then
                       let uu____14957 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____14957
                     else FStar_Pervasives_Native.None)
             in
          (match uu____14920 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____14961 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____14969 =
      let uu____14970 = FStar_Syntax_Util.un_uinst l  in
      uu____14970.FStar_Syntax_Syntax.n  in
    match uu____14969 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____14975 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____15011)::uu____15012 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____15031 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____15040,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____15041))::uu____15042 -> bs
      | uu____15060 ->
          let uu____15061 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____15061 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____15065 =
                 let uu____15066 = FStar_Syntax_Subst.compress t  in
                 uu____15066.FStar_Syntax_Syntax.n  in
               (match uu____15065 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____15070) ->
                    let uu____15091 =
                      FStar_Util.prefix_until
                        (fun uu___10_15131  ->
                           match uu___10_15131 with
                           | (uu____15139,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____15140)) ->
                               false
                           | uu____15145 -> true) bs'
                       in
                    (match uu____15091 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____15181,uu____15182) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____15254,uu____15255) ->
                         let uu____15328 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____15348  ->
                                   match uu____15348 with
                                   | (x,uu____15357) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____15328
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____15406  ->
                                     match uu____15406 with
                                     | (x,i) ->
                                         let uu____15425 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____15425, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____15436 -> bs))
  
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
            let uu____15465 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____15465
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
          let uu____15496 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____15496
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
        (let uu____15539 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____15539
         then
           ((let uu____15544 = FStar_Ident.text_of_lid lident  in
             d uu____15544);
            (let uu____15546 = FStar_Ident.text_of_lid lident  in
             let uu____15548 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____15546 uu____15548))
         else ());
        (let fv =
           let uu____15554 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____15554
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
         let uu____15566 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1841_15568 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1841_15568.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1841_15568.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1841_15568.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1841_15568.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___1841_15568.FStar_Syntax_Syntax.sigopts)
           }), uu____15566))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_15586 =
        match uu___11_15586 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____15589 -> false  in
      let reducibility uu___12_15597 =
        match uu___12_15597 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____15604 -> false  in
      let assumption uu___13_15612 =
        match uu___13_15612 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____15616 -> false  in
      let reification uu___14_15624 =
        match uu___14_15624 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____15627 -> true
        | uu____15629 -> false  in
      let inferred uu___15_15637 =
        match uu___15_15637 with
        | FStar_Syntax_Syntax.Discriminator uu____15639 -> true
        | FStar_Syntax_Syntax.Projector uu____15641 -> true
        | FStar_Syntax_Syntax.RecordType uu____15647 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____15657 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____15670 -> false  in
      let has_eq uu___16_15678 =
        match uu___16_15678 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____15682 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____15761 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____15768 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____15801 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____15801))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____15832 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____15832
                       FStar_Parser_Const.erasable_attr)))
           in
        let se_has_erasable_attr =
          FStar_Syntax_Util.has_attribute se1.FStar_Syntax_Syntax.sigattrs
            FStar_Parser_Const.erasable_attr
           in
        if
          (val_exists && val_has_erasable_attr) &&
            (Prims.op_Negation se_has_erasable_attr)
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributes between declaration and definition: Declaration is marked `erasable` but the definition is not")
            r
        else ();
        if
          (val_exists && (Prims.op_Negation val_has_erasable_attr)) &&
            se_has_erasable_attr
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributed between declaration and definition: Definition is marked `erasable` but the declaration is not")
            r
        else ();
        if se_has_erasable_attr
        then
          (match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_bundle uu____15852 ->
               let uu____15861 =
                 let uu____15863 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_15869  ->
                           match uu___17_15869 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____15872 -> false))
                    in
                 Prims.op_Negation uu____15863  in
               if uu____15861
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____15879 -> ()
           | uu____15886 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions")
                 r)
        else ()  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____15900 =
        let uu____15902 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_15908  ->
                  match uu___18_15908 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____15911 -> false))
           in
        FStar_All.pipe_right uu____15902 Prims.op_Negation  in
      if uu____15900
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____15932 =
            let uu____15938 =
              let uu____15940 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____15940 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____15938)  in
          FStar_Errors.raise_error uu____15932 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____15958 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____15966 =
            let uu____15968 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____15968  in
          if uu____15966 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____15979),uu____15980) ->
              ((let uu____15992 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____15992
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____16001 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____16001
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____16012 ->
              ((let uu____16022 =
                  let uu____16024 =
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
                  Prims.op_Negation uu____16024  in
                if uu____16022 then err'1 () else ());
               (let uu____16034 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_16040  ->
                           match uu___19_16040 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____16043 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____16034
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____16049 ->
              let uu____16056 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____16056 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____16064 ->
              let uu____16071 =
                let uu____16073 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____16073  in
              if uu____16071 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____16083 ->
              let uu____16084 =
                let uu____16086 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____16086  in
              if uu____16084 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16096 ->
              let uu____16109 =
                let uu____16111 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____16111  in
              if uu____16109 then err'1 () else ()
          | uu____16121 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____16160 =
          let uu____16161 = FStar_Syntax_Subst.compress t1  in
          uu____16161.FStar_Syntax_Syntax.n  in
        match uu____16160 with
        | FStar_Syntax_Syntax.Tm_arrow uu____16165 ->
            let uu____16180 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____16180 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____16213;
               FStar_Syntax_Syntax.index = uu____16214;
               FStar_Syntax_Syntax.sort = t2;_},uu____16216)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____16225) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____16251) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____16257 -> false
      
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
        (let uu____16267 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____16267
         then
           let uu____16272 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____16272
         else ());
        res
       in aux g t
  
let (fresh_effect_repr :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.universe ->
              FStar_Syntax_Syntax.term ->
                (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun signature_ts  ->
          fun repr_ts_opt  ->
            fun u  ->
              fun a_tm  ->
                let fail1 t =
                  let uu____16337 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____16337 r  in
                let uu____16347 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____16347 with
                | (uu____16356,signature) ->
                    let uu____16358 =
                      let uu____16359 = FStar_Syntax_Subst.compress signature
                         in
                      uu____16359.FStar_Syntax_Syntax.n  in
                    (match uu____16358 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16367) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____16415 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____16430 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____16432 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____16430 eff_name.FStar_Ident.str
                                       uu____16432) r
                                 in
                              (match uu____16415 with
                               | (is,g) ->
                                   let uu____16445 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____16447 =
                                             let uu____16448 =
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 is
                                                in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = [u];
                                               FStar_Syntax_Syntax.effect_name
                                                 = eff_name;
                                               FStar_Syntax_Syntax.result_typ
                                                 = a_tm;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____16448;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____16447
                                            in
                                         let uu____16467 =
                                           let uu____16474 =
                                             let uu____16475 =
                                               let uu____16490 =
                                                 let uu____16499 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____16499]  in
                                               (uu____16490, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____16475
                                              in
                                           FStar_Syntax_Syntax.mk uu____16474
                                            in
                                         uu____16467
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____16530 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____16530
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____16539 =
                                           let uu____16544 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____16544
                                            in
                                         uu____16539
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____16445, g))
                          | uu____16553 -> fail1 signature)
                     | uu____16554 -> fail1 signature)
  
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
            let uu____16585 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____16585
              (fun ed  ->
                 let uu____16593 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____16593 u a_tm)
  
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
              let uu____16629 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____16629 with
              | (uu____16634,sig_tm) ->
                  let fail1 t =
                    let uu____16642 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____16642 r  in
                  let uu____16648 =
                    let uu____16649 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____16649.FStar_Syntax_Syntax.n  in
                  (match uu____16648 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16653) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____16676)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____16698 -> fail1 sig_tm)
                   | uu____16699 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____16730 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____16730
           then
             let uu____16735 = FStar_Syntax_Print.comp_to_string c  in
             let uu____16737 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____16735 uu____16737
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered1 =
             let err uu____16767 =
               let uu____16768 =
                 let uu____16774 =
                   let uu____16776 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____16778 = FStar_Util.string_of_bool is_layered1
                      in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____16776 uu____16778
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____16774)  in
               FStar_Errors.raise_error uu____16768 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered1
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____16790,uu____16791::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____16859 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____16864,c1) ->
                    let uu____16886 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____16886
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____16921 -> err ())
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____16923 =
             let uu____16934 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____16935 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____16934, (ct.FStar_Syntax_Syntax.result_typ), uu____16935)
              in
           match uu____16923 with
           | (u,a,c_is) ->
               let uu____16983 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____16983 with
                | (uu____16992,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____17003 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____17005 = FStar_Ident.string_of_lid tgt  in
                      let uu____17007 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____17003 uu____17005 s uu____17007
                       in
                    let uu____17010 =
                      let uu____17043 =
                        let uu____17044 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____17044.FStar_Syntax_Syntax.n  in
                      match uu____17043 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____17108 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____17108 with
                           | (a_b::bs1,c2) ->
                               let uu____17168 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____17230 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____17168, uu____17230))
                      | uu____17257 ->
                          let uu____17258 =
                            let uu____17264 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____17264)
                             in
                          FStar_Errors.raise_error uu____17258 r
                       in
                    (match uu____17010 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____17382 =
                           let uu____17389 =
                             let uu____17390 =
                               let uu____17391 =
                                 let uu____17398 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____17398, a)  in
                               FStar_Syntax_Syntax.NT uu____17391  in
                             [uu____17390]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____17389
                             (fun b  ->
                                let uu____17415 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____17417 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____17419 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____17421 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____17415 uu____17417 uu____17419
                                  uu____17421) r
                            in
                         (match uu____17382 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____17435 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____17435
                                then
                                  let uu____17440 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____17449 =
                                             let uu____17451 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____17451
                                              in
                                           Prims.op_Hat s uu____17449) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____17440
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____17482 =
                                           let uu____17489 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____17489, t)  in
                                         FStar_Syntax_Syntax.NT uu____17482)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____17508 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____17508
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____17514 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____17514
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____17523 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____17523)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____17527 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____17527
                                   in
                                let c1 =
                                  let uu____17530 =
                                    let uu____17531 =
                                      let uu____17542 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____17542
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____17531;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____17530  in
                                (let uu____17562 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____17562
                                 then
                                   let uu____17567 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____17567
                                 else ());
                                (let uu____17572 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____17572))))))))
  
let (lift_tf_layered_effect_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun sub1  ->
      fun u  ->
        fun a  ->
          fun e  ->
            let lift =
              let uu____17602 =
                let uu____17607 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____17607
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____17602 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____17650 =
                let uu____17651 =
                  let uu____17654 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____17654
                    FStar_Syntax_Subst.compress
                   in
                uu____17651.FStar_Syntax_Syntax.n  in
              match uu____17650 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____17677::bs,uu____17679)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____17719 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____17719
                    FStar_Pervasives_Native.fst
              | uu____17825 ->
                  let uu____17826 =
                    let uu____17832 =
                      let uu____17834 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____17834
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____17832)  in
                  FStar_Errors.raise_error uu____17826
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let e_reified =
              let uu____17851 =
                let uu____17854 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.source
                    (FStar_TypeChecker_Env.get_effect_decl env)
                   in
                FStar_All.pipe_right uu____17854
                  FStar_Syntax_Util.get_eff_repr
                 in
              match uu____17851 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17857 =
                    let uu____17858 =
                      FStar_Syntax_Syntax.null_binder
                        FStar_Syntax_Syntax.t_unit
                       in
                    [uu____17858]  in
                  FStar_Syntax_Util.abs uu____17857 e
                    FStar_Pervasives_Native.None
              | uu____17877 ->
                  reify_body env [FStar_TypeChecker_Env.Inlining] e
               in
            let args =
              let uu____17891 = FStar_Syntax_Syntax.as_arg a  in
              let uu____17900 =
                let uu____17911 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____17947  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____17954 =
                  let uu____17965 = FStar_Syntax_Syntax.as_arg e_reified  in
                  [uu____17965]  in
                FStar_List.append uu____17911 uu____17954  in
              uu____17891 :: uu____17900  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____18029 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____18029
      then
        let uu____18032 =
          let uu____18045 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____18045
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____18032;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18080 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____18080 with
           | (uu____18089,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____18108 =
                 let uu____18109 =
                   let uu___2206_18110 = ct  in
                   let uu____18111 =
                     let uu____18122 =
                       let uu____18131 =
                         let uu____18132 =
                           let uu____18139 =
                             let uu____18140 =
                               let uu____18157 =
                                 let uu____18168 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____18168; wp]  in
                               (lift_t, uu____18157)  in
                             FStar_Syntax_Syntax.Tm_app uu____18140  in
                           FStar_Syntax_Syntax.mk uu____18139  in
                         uu____18132 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____18131
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____18122]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2206_18110.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2206_18110.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____18111;
                     FStar_Syntax_Syntax.flags =
                       (uu___2206_18110.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____18109  in
               (uu____18108, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____18268 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____18268 with
           | (uu____18275,lift_t) ->
               let uu____18277 =
                 let uu____18284 =
                   let uu____18285 =
                     let uu____18302 =
                       let uu____18313 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____18322 =
                         let uu____18333 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____18342 =
                           let uu____18353 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____18353]  in
                         uu____18333 :: uu____18342  in
                       uu____18313 :: uu____18322  in
                     (lift_t, uu____18302)  in
                   FStar_Syntax_Syntax.Tm_app uu____18285  in
                 FStar_Syntax_Syntax.mk uu____18284  in
               uu____18277 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____18406 =
           let uu____18419 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____18419 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____18406;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____18455  ->
                        fun uu____18456  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____18486 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____18486 with
        | (uu____18491,t) ->
            let err n1 =
              let uu____18501 =
                let uu____18507 =
                  let uu____18509 = FStar_Ident.string_of_lid datacon  in
                  let uu____18511 = FStar_Util.string_of_int n1  in
                  let uu____18513 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____18509 uu____18511 uu____18513
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____18507)
                 in
              let uu____18517 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____18501 uu____18517  in
            let uu____18518 =
              let uu____18519 = FStar_Syntax_Subst.compress t  in
              uu____18519.FStar_Syntax_Syntax.n  in
            (match uu____18518 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18523) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____18578  ->
                           match uu____18578 with
                           | (uu____18586,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____18595 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____18627 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____18627
                      FStar_Pervasives_Native.fst)
             | uu____18638 -> err Prims.int_zero)
  