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
          | FStar_Syntax_Syntax.Tm_refine (b,phi) ->
              let is_unit1 =
                match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.unit_lid
                | uu____4833 -> false  in
              if is_unit1
              then
                let uu____4840 =
                  let uu____4842 =
                    let uu____4843 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____4843
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____4842
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____4840
                 then
                   let uu____4852 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____4852 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____4896 =
                           let uu____4899 =
                             let uu____4900 =
                               let uu____4907 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4907, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____4900  in
                           [uu____4899]  in
                         FStar_Syntax_Subst.subst uu____4896 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____4920 = close_wp_comp env [x] c  in
                    (uu____4920, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____4923 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____4951  ->
            match uu____4951 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4971 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____4971 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____4984 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____4984
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____4994 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____4994
                       then
                         let uu____4999 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____4999
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5006 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____5006
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5015 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____5015
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5022 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5022
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____5038 =
                  let uu____5039 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5039
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____5047 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____5047, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____5050 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____5050 with
                     | (c1,g_c1) ->
                         let uu____5061 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____5061 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____5081  ->
                                    let uu____5082 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____5084 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____5089 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____5082 uu____5084 uu____5089);
                               (let aux uu____5107 =
                                  let uu____5108 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____5108
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5139
                                        ->
                                        let uu____5140 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5140
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5172 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5172
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____5219 =
                                  let aux_with_trivial_guard uu____5249 =
                                    let uu____5250 = aux ()  in
                                    match uu____5250 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c,
                                            FStar_TypeChecker_Env.trivial_guard,
                                            reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____5308 =
                                    let uu____5310 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____5310  in
                                  if uu____5308
                                  then
                                    let uu____5326 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____5326
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           FStar_TypeChecker_Env.trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5353 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5353))
                                  else
                                    (let uu____5370 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____5370
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___661_5416 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___661_5416.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___661_5416.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____5417 =
                                           maybe_capture_unit_refinement env
                                             x1.FStar_Syntax_Syntax.sort x1 c
                                            in
                                         match uu____5417 with
                                         | (c3,g_c) ->
                                             FStar_Util.Inl (c3, g_c, reason)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____5475 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____5475
                                             (close1 x "c1 Tot")
                                       | (uu____5491,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____5516,uu____5517) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____5532 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____5532
                                        then
                                          let uu____5547 =
                                            let uu____5555 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____5555,
                                              FStar_TypeChecker_Env.trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____5547
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____5568 = try_simplify ()  in
                                match uu____5568 with
                                | FStar_Util.Inl (c,g_c,reason) ->
                                    (debug1
                                       (fun uu____5603  ->
                                          let uu____5604 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____5604);
                                     (let uu____5607 =
                                        let uu____5608 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c1 g_c2
                                           in
                                        FStar_TypeChecker_Env.conj_guard g_c
                                          uu____5608
                                         in
                                      (c, uu____5607)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____5622  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____5648 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____5648 with
                                        | (c,g_bind) ->
                                            let uu____5659 =
                                              let uu____5660 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5660 g_bind
                                               in
                                            (c, uu____5659)
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
                                        let uu____5687 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5687 with
                                        | (m,uu____5699,lift2) ->
                                            let uu____5701 =
                                              lift_comp env c22 lift2  in
                                            (match uu____5701 with
                                             | (c23,g2) ->
                                                 let uu____5712 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____5712 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____5728 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5728
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____5738 =
                                                          let uu____5743 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____5744 =
                                                            let uu____5745 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5754 =
                                                              let uu____5765
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5765]
                                                               in
                                                            uu____5745 ::
                                                              uu____5754
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5743
                                                            uu____5744
                                                           in
                                                        uu____5738
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5798 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____5798 with
                                                       | (c,g_s) ->
                                                           let uu____5813 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____5813))))
                                         in
                                      let uu____5814 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5830 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____5830, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____5814 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____5846 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____5846
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____5855 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____5855
                                             then
                                               (debug1
                                                  (fun uu____5869  ->
                                                     let uu____5870 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____5872 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____5870 uu____5872);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____5880 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____5883 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____5883)
                                                   in
                                                if uu____5880
                                                then
                                                  let e1' =
                                                    let uu____5908 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____5908
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____5920  ->
                                                        let uu____5921 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____5923 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____5921
                                                          uu____5923);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____5938  ->
                                                        let uu____5939 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5941 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____5939
                                                          uu____5941);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____5948 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____5948
                                                       in
                                                    let uu____5949 =
                                                      let uu____5954 =
                                                        let uu____5955 =
                                                          let uu____5956 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____5956]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____5955
                                                         in
                                                      weaken_comp uu____5954
                                                        c21 x_eq_e
                                                       in
                                                    match uu____5949 with
                                                    | (c22,g_w) ->
                                                        let uu____5981 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____5981
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____5992 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____5992))))))
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
      | uu____6009 -> g2
  
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
            (let uu____6033 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6033)
           in
        let flags =
          if should_return1
          then
            let uu____6041 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6041
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6059 =
          let uu____6060 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6060 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6073 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6073
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6081 =
                  let uu____6083 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6083  in
                (if uu____6081
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___780_6092 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___780_6092.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___780_6092.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___780_6092.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6093 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6093, g_c)
                 else
                   (let uu____6096 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6096, g_c)))
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
                   let uu____6107 =
                     let uu____6108 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6108
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6107
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6111 =
                   let uu____6116 =
                     let uu____6117 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6117
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6116  in
                 match uu____6111 with
                 | (bind_c,g_bind) ->
                     let uu____6126 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6127 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6126, uu____6127))
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
            fun uu____6163  ->
              match uu____6163 with
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
                    let uu____6175 =
                      ((let uu____6179 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6179) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6175
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6197 =
        let uu____6198 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6198  in
      FStar_Syntax_Syntax.fvar uu____6197 FStar_Syntax_Syntax.delta_constant
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
                  let uu____6248 =
                    let uu____6253 =
                      let uu____6254 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____6254 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____6253 [u_a]
                     in
                  match uu____6248 with
                  | (uu____6265,conjunction) ->
                      let uu____6267 =
                        let uu____6276 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____6291 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____6276, uu____6291)  in
                      (match uu____6267 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____6337 =
                               let uu____6339 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____6339 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____6337)
                              in
                           let uu____6343 =
                             let uu____6388 =
                               let uu____6389 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____6389.FStar_Syntax_Syntax.n  in
                             match uu____6388 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____6438) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____6470 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____6470 with
                                  | (a_b::bs1,body1) ->
                                      let uu____6542 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____6542 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____6690 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____6690)))
                             | uu____6723 ->
                                 let uu____6724 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____6724 r
                              in
                           (match uu____6343 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____6849 =
                                  let uu____6856 =
                                    let uu____6857 =
                                      let uu____6858 =
                                        let uu____6865 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____6865, a)  in
                                      FStar_Syntax_Syntax.NT uu____6858  in
                                    [uu____6857]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____6856
                                    (fun b  ->
                                       let uu____6881 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____6883 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____6885 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____6881 uu____6883 uu____6885) r
                                   in
                                (match uu____6849 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____6923 =
                                                let uu____6930 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____6930, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____6923) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____6969 =
                                           let uu____6970 =
                                             let uu____6973 =
                                               let uu____6974 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____6974.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____6973
                                              in
                                           uu____6970.FStar_Syntax_Syntax.n
                                            in
                                         match uu____6969 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____6985,uu____6986::is) ->
                                             let uu____7028 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7028
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7061 ->
                                             let uu____7062 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7062 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____7078 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7078)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____7083 =
                                           let uu____7084 =
                                             let uu____7087 =
                                               let uu____7088 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7088.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7087
                                              in
                                           uu____7084.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7083 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7099,uu____7100::is) ->
                                             let uu____7142 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7142
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7175 ->
                                             let uu____7176 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7176 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____7192 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7192)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____7197 =
                                         let uu____7198 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____7198.FStar_Syntax_Syntax.n  in
                                       match uu____7197 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7203,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____7258 ->
                                           let uu____7259 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____7259 r
                                        in
                                     let uu____7268 =
                                       let uu____7269 =
                                         let uu____7270 =
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
                                             uu____7270;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____7269
                                        in
                                     let uu____7293 =
                                       let uu____7294 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____7294 g_guard
                                        in
                                     (uu____7268, uu____7293))))
  
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
                fun uu____7339  ->
                  let if_then_else1 =
                    let uu____7345 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____7345 FStar_Util.must  in
                  let uu____7352 = destruct_wp_comp ct1  in
                  match uu____7352 with
                  | (uu____7363,uu____7364,wp_t) ->
                      let uu____7366 = destruct_wp_comp ct2  in
                      (match uu____7366 with
                       | (uu____7377,uu____7378,wp_e) ->
                           let wp =
                             let uu____7383 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____7384 =
                               let uu____7389 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____7390 =
                                 let uu____7391 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____7400 =
                                   let uu____7411 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____7420 =
                                     let uu____7431 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____7440 =
                                       let uu____7451 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____7451]  in
                                     uu____7431 :: uu____7440  in
                                   uu____7411 :: uu____7420  in
                                 uu____7391 :: uu____7400  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____7389
                                 uu____7390
                                in
                             uu____7384 FStar_Pervasives_Native.None
                               uu____7383
                              in
                           let uu____7500 = mk_comp ed u_a a wp []  in
                           (uu____7500, FStar_TypeChecker_Env.trivial_guard))
  
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
               fun uu____7570  ->
                 match uu____7570 with
                 | (uu____7584,eff_label,uu____7586,uu____7587) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____7600 =
          let uu____7608 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____7646  ->
                    match uu____7646 with
                    | (uu____7661,uu____7662,flags,uu____7664) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_7681  ->
                                match uu___5_7681 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____7684 -> false))))
             in
          if uu____7608
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____7600 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____7721 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____7723 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____7723
              then
                let uu____7730 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____7730, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____7737 =
                       let uu____7746 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7746]  in
                     let uu____7765 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7737 uu____7765  in
                   let kwp =
                     let uu____7771 =
                       let uu____7780 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7780]  in
                     let uu____7799 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7771 uu____7799  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7806 =
                       let uu____7807 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7807]  in
                     let uu____7826 =
                       let uu____7829 =
                         let uu____7836 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7836
                          in
                       let uu____7837 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7829 uu____7837  in
                     FStar_Syntax_Util.abs uu____7806 uu____7826
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
                   let uu____7861 =
                     should_not_inline_whole_match ||
                       (let uu____7864 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7864)
                      in
                   if uu____7861 then cthen true else cthen false  in
                 let uu____7871 =
                   FStar_List.fold_right
                     (fun uu____7924  ->
                        fun uu____7925  ->
                          match (uu____7924, uu____7925) with
                          | ((g,eff_label,uu____7979,cthen),(uu____7981,celse,g_comp))
                              ->
                              let uu____8022 =
                                let uu____8027 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____8027
                                 in
                              (match uu____8022 with
                               | (cthen1,gthen) ->
                                   let uu____8038 =
                                     let uu____8047 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____8047 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____8070 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____8071 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____8070, uu____8071, g_lift)
                                      in
                                   (match uu____8038 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          let uu____8121 =
                                            FStar_All.pipe_right md
                                              FStar_Syntax_Util.is_layered
                                             in
                                          if uu____8121
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____8155 =
                                          let uu____8160 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____8160
                                           in
                                        (match uu____8155 with
                                         | (c,g_conjunction) ->
                                             let uu____8171 =
                                               let uu____8172 =
                                                 let uu____8173 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____8173 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____8172 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____8171)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____7871 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____8207::[] -> (comp, g_comp)
                      | uu____8250 ->
                          let uu____8267 =
                            let uu____8269 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            FStar_All.pipe_right uu____8269
                              FStar_Syntax_Util.is_layered
                             in
                          if uu____8267
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
                             let uu____8282 = destruct_wp_comp comp1  in
                             match uu____8282 with
                             | (uu____8293,uu____8294,wp) ->
                                 let ite_wp =
                                   let uu____8297 =
                                     FStar_All.pipe_right md1
                                       FStar_Syntax_Util.get_wp_ite_combinator
                                      in
                                   FStar_All.pipe_right uu____8297
                                     FStar_Util.must
                                    in
                                 let wp1 =
                                   let uu____8307 =
                                     let uu____8312 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_res_t] env md1 ite_wp
                                        in
                                     let uu____8313 =
                                       let uu____8314 =
                                         FStar_Syntax_Syntax.as_arg res_t  in
                                       let uu____8323 =
                                         let uu____8334 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [uu____8334]  in
                                       uu____8314 :: uu____8323  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____8312
                                       uu____8313
                                      in
                                   uu____8307 FStar_Pervasives_Native.None
                                     wp.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____8367 =
                                   mk_comp md1 u_res_t res_t wp1
                                     bind_cases_flags
                                    in
                                 (uu____8367, g_comp))))
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
          let uu____8401 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____8401 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____8417 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____8423 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____8417 uu____8423
              else
                (let uu____8432 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____8438 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____8432 uu____8438)
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
          let uu____8463 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____8463
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____8466 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____8466
        then u_res
        else
          (let is_total =
             let uu____8473 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____8473
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____8484 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____8484 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8487 =
                    let uu____8493 =
                      let uu____8495 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____8495
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____8493)
                     in
                  FStar_Errors.raise_error uu____8487
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
      let uu____8519 = destruct_wp_comp ct  in
      match uu____8519 with
      | (u_t,t,wp) ->
          let vc =
            let uu____8538 = FStar_TypeChecker_Env.get_range env  in
            let uu____8539 =
              let uu____8544 =
                let uu____8545 =
                  let uu____8546 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____8546 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____8545
                 in
              let uu____8553 =
                let uu____8554 = FStar_Syntax_Syntax.as_arg t  in
                let uu____8563 =
                  let uu____8574 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____8574]  in
                uu____8554 :: uu____8563  in
              FStar_Syntax_Syntax.mk_Tm_app uu____8544 uu____8553  in
            uu____8539 FStar_Pervasives_Native.None uu____8538  in
          let uu____8607 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____8607)
  
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
                  let uu____8662 = FStar_TypeChecker_Env.try_lookup_lid env f
                     in
                  match uu____8662 with
                  | FStar_Pervasives_Native.Some uu____8677 ->
                      ((let uu____8695 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____8695
                        then
                          let uu____8699 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____8699
                        else ());
                       (let coercion =
                          let uu____8705 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____8705
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____8712 =
                            let uu____8713 =
                              let uu____8714 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____8714
                               in
                            (FStar_Pervasives_Native.None, uu____8713)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____8712
                           in
                        let e1 =
                          let uu____8720 =
                            let uu____8725 =
                              let uu____8726 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____8726]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____8725
                             in
                          uu____8720 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8760 =
                          let uu____8766 =
                            let uu____8768 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____8768
                             in
                          (FStar_Errors.Warning_CoercionNotFound, uu____8766)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____8760);
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
            (((let uu____8805 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____8805) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc)
          else
            (let is_t_term t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8822 =
                 let uu____8823 = FStar_Syntax_Subst.compress t2  in
                 uu____8823.FStar_Syntax_Syntax.n  in
               match uu____8822 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____8828 -> false  in
             let is_t_term_view t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8838 =
                 let uu____8839 = FStar_Syntax_Subst.compress t2  in
                 uu____8839.FStar_Syntax_Syntax.n  in
               match uu____8838 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____8844 -> false  in
             let is_type1 t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8854 =
                 let uu____8855 = FStar_Syntax_Subst.compress t2  in
                 uu____8855.FStar_Syntax_Syntax.n  in
               match uu____8854 with
               | FStar_Syntax_Syntax.Tm_type uu____8859 -> true
               | uu____8861 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____8864 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____8864 with
             | (head1,args) ->
                 ((let uu____8912 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____8912
                   then
                     let uu____8916 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____8918 = FStar_Syntax_Print.term_to_string e  in
                     let uu____8920 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____8922 = FStar_Syntax_Print.term_to_string t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____8916 uu____8918 uu____8920 uu____8922
                   else ());
                  (let is_erased env1 t1 t2 =
                     let uu____8944 = FStar_Syntax_Util.head_and_args t2  in
                     match uu____8944 with
                     | (head2,args1) ->
                         let uu____8988 =
                           let uu____9003 =
                             let uu____9004 =
                               FStar_Syntax_Util.un_uinst head2  in
                             uu____9004.FStar_Syntax_Syntax.n  in
                           (uu____9003, args1)  in
                         (match uu____8988 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(x,FStar_Pervasives_Native.None )::[]) ->
                              (FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.erased_lid)
                                && (FStar_Syntax_Util.term_eq x t1)
                          | uu____9052 -> false)
                      in
                   let uu____9068 =
                     let uu____9083 =
                       let uu____9084 = FStar_Syntax_Util.un_uinst head1  in
                       uu____9084.FStar_Syntax_Syntax.n  in
                     (uu____9083, args)  in
                   match uu____9068 with
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
                   | uu____9209 when is_erased env t res_typ ->
                       let uu____9224 =
                         let uu____9225 =
                           env.FStar_TypeChecker_Env.universe_of env t  in
                         [uu____9225]  in
                       let uu____9226 =
                         let uu____9227 = FStar_Syntax_Syntax.iarg t  in
                         [uu____9227]  in
                       coerce_with env e lc t FStar_Parser_Const.reveal
                         uu____9224 uu____9226 FStar_Syntax_Syntax.mk_GTotal
                   | uu____9252 when is_erased env res_typ t ->
                       let uu____9267 =
                         let uu____9268 =
                           env.FStar_TypeChecker_Env.universe_of env res_typ
                            in
                         [uu____9268]  in
                       let uu____9269 =
                         let uu____9270 = FStar_Syntax_Syntax.iarg res_typ
                            in
                         [uu____9270]  in
                       coerce_with env e lc t FStar_Parser_Const.hide
                         uu____9267 uu____9269 FStar_Syntax_Syntax.mk_Total
                   | uu____9295 -> (e, lc))))
  
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
        let uu____9340 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____9340 with
        | (hd1,args) ->
            let uu____9389 =
              let uu____9404 =
                let uu____9405 = FStar_Syntax_Subst.compress hd1  in
                uu____9405.FStar_Syntax_Syntax.n  in
              (uu____9404, args)  in
            (match uu____9389 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____9443 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Total
                    in
                 FStar_All.pipe_left
                   (fun _9470  -> FStar_Pervasives_Native.Some _9470)
                   uu____9443
             | uu____9471 -> FStar_Pervasives_Native.None)
  
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
          (let uu____9524 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____9524
           then
             let uu____9527 = FStar_Syntax_Print.term_to_string e  in
             let uu____9529 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____9531 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____9527 uu____9529 uu____9531
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____9541 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____9541 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____9566 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____9592 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____9592, false)
             else
               (let uu____9602 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____9602, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____9615) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____9627 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____9627
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1135_9643 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1135_9643.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1135_9643.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1135_9643.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____9650 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____9650 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____9666 =
                      let uu____9667 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____9667 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____9687 =
                            let uu____9689 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____9689 = FStar_Syntax_Util.Equal  in
                          if uu____9687
                          then
                            ((let uu____9696 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____9696
                              then
                                let uu____9700 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____9702 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____9700 uu____9702
                              else ());
                             (let uu____9707 = set_result_typ1 c  in
                              (uu____9707, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____9714 ->
                                   true
                               | uu____9722 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____9731 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____9731
                                  in
                               let lc1 =
                                 let uu____9733 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____9734 =
                                   let uu____9735 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____9735)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____9733 uu____9734
                                  in
                               ((let uu____9739 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____9739
                                 then
                                   let uu____9743 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____9745 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____9747 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____9749 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____9743 uu____9745 uu____9747
                                     uu____9749
                                 else ());
                                (let uu____9754 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____9754 with
                                 | (c1,g_lc) ->
                                     let uu____9765 = set_result_typ1 c1  in
                                     let uu____9766 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____9765, uu____9766)))
                             else
                               ((let uu____9770 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____9770
                                 then
                                   let uu____9774 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____9776 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____9774 uu____9776
                                 else ());
                                (let uu____9781 = set_result_typ1 c  in
                                 (uu____9781, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1172_9785 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1172_9785.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1172_9785.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1172_9785.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____9795 =
                      let uu____9796 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____9796
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____9806 =
                           let uu____9807 = FStar_Syntax_Subst.compress f1
                              in
                           uu____9807.FStar_Syntax_Syntax.n  in
                         match uu____9806 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____9814,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____9816;
                                           FStar_Syntax_Syntax.vars =
                                             uu____9817;_},uu____9818)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1188_9844 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1188_9844.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1188_9844.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1188_9844.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____9845 ->
                             let uu____9846 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____9846 with
                              | (c,g_c) ->
                                  ((let uu____9858 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____9858
                                    then
                                      let uu____9862 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____9864 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____9866 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____9868 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____9862 uu____9864 uu____9866
                                        uu____9868
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
                                        let uu____9881 =
                                          let uu____9886 =
                                            let uu____9887 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____9887]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____9886
                                           in
                                        uu____9881
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____9914 =
                                      let uu____9919 =
                                        FStar_All.pipe_left
                                          (fun _9940  ->
                                             FStar_Pervasives_Native.Some
                                               _9940)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____9941 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____9942 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____9943 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____9919
                                        uu____9941 e uu____9942 uu____9943
                                       in
                                    match uu____9914 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1206_9951 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1206_9951.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1206_9951.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____9953 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____9953
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____9956 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____9956 with
                                         | (c2,g_lc) ->
                                             ((let uu____9968 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____9968
                                               then
                                                 let uu____9972 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____9972
                                               else ());
                                              (let uu____9977 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____9977))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_9986  ->
                              match uu___6_9986 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____9989 -> []))
                       in
                    let lc1 =
                      let uu____9991 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____9991 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1222_9993 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1222_9993.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1222_9993.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1222_9993.FStar_TypeChecker_Common.implicits)
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
        let uu____10029 =
          let uu____10032 =
            let uu____10037 =
              let uu____10038 =
                let uu____10047 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____10047  in
              [uu____10038]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____10037  in
          uu____10032 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____10029  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____10070 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____10070
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____10089 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____10105 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____10122 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____10122
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____10138)::(ens,uu____10140)::uu____10141 ->
                    let uu____10184 =
                      let uu____10187 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____10187  in
                    let uu____10188 =
                      let uu____10189 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____10189  in
                    (uu____10184, uu____10188)
                | uu____10192 ->
                    let uu____10203 =
                      let uu____10209 =
                        let uu____10211 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____10211
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____10209)
                       in
                    FStar_Errors.raise_error uu____10203
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____10231)::uu____10232 ->
                    let uu____10259 =
                      let uu____10264 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____10264
                       in
                    (match uu____10259 with
                     | (us_r,uu____10296) ->
                         let uu____10297 =
                           let uu____10302 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____10302
                            in
                         (match uu____10297 with
                          | (us_e,uu____10334) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____10337 =
                                  let uu____10338 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10338
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10337
                                  us_r
                                 in
                              let as_ens =
                                let uu____10340 =
                                  let uu____10341 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10341
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10340
                                  us_e
                                 in
                              let req =
                                let uu____10345 =
                                  let uu____10350 =
                                    let uu____10351 =
                                      let uu____10362 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10362]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10351
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____10350
                                   in
                                uu____10345 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____10402 =
                                  let uu____10407 =
                                    let uu____10408 =
                                      let uu____10419 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10419]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10408
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____10407
                                   in
                                uu____10402 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____10456 =
                                let uu____10459 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____10459  in
                              let uu____10460 =
                                let uu____10461 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____10461  in
                              (uu____10456, uu____10460)))
                | uu____10464 -> failwith "Impossible"))
  
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
        (let uu____10503 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____10503
         then
           let uu____10508 = FStar_Syntax_Print.term_to_string tm  in
           let uu____10510 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____10508
             uu____10510
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
          (let uu____10569 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____10569
           then
             let uu____10574 = FStar_Syntax_Print.term_to_string tm  in
             let uu____10576 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____10574
               uu____10576
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____10587 =
      let uu____10589 =
        let uu____10590 = FStar_Syntax_Subst.compress t  in
        uu____10590.FStar_Syntax_Syntax.n  in
      match uu____10589 with
      | FStar_Syntax_Syntax.Tm_app uu____10594 -> false
      | uu____10612 -> true  in
    if uu____10587
    then t
    else
      (let uu____10617 = FStar_Syntax_Util.head_and_args t  in
       match uu____10617 with
       | (head1,args) ->
           let uu____10660 =
             let uu____10662 =
               let uu____10663 = FStar_Syntax_Subst.compress head1  in
               uu____10663.FStar_Syntax_Syntax.n  in
             match uu____10662 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____10668 -> false  in
           if uu____10660
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____10700 ->
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
          ((let uu____10747 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____10747
            then
              let uu____10750 = FStar_Syntax_Print.term_to_string e  in
              let uu____10752 = FStar_Syntax_Print.term_to_string t  in
              let uu____10754 =
                let uu____10756 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____10756
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____10750 uu____10752 uu____10754
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____10769 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____10769 with
              | (formals,uu____10785) ->
                  let n_implicits =
                    let uu____10807 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____10885  ->
                              match uu____10885 with
                              | (uu____10893,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____10900 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____10900 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____10807 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____11025 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____11025 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____11039 =
                      let uu____11045 =
                        let uu____11047 = FStar_Util.string_of_int n_expected
                           in
                        let uu____11049 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____11051 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____11047 uu____11049 uu____11051
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____11045)
                       in
                    let uu____11055 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____11039 uu____11055
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_11073 =
              match uu___7_11073 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____11116 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____11116 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _11247,uu____11234)
                           when _11247 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____11280,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____11282))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____11316 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____11316 with
                            | (v1,uu____11357,g) ->
                                ((let uu____11372 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____11372
                                  then
                                    let uu____11375 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____11375
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____11385 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____11385 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____11478 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____11478))))
                       | (uu____11505,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____11542 =
                             let uu____11555 =
                               let uu____11562 =
                                 let uu____11567 = FStar_Dyn.mkdyn env  in
                                 (uu____11567, tau)  in
                               FStar_Pervasives_Native.Some uu____11562  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____11555
                              in
                           (match uu____11542 with
                            | (v1,uu____11600,g) ->
                                ((let uu____11615 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____11615
                                  then
                                    let uu____11618 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____11618
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____11628 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____11628 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____11721 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____11721))))
                       | (uu____11748,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____11796 =
                       let uu____11823 = inst_n_binders t1  in
                       aux [] uu____11823 bs1  in
                     (match uu____11796 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____11895) -> (e, torig, guard)
                           | (uu____11926,[]) when
                               let uu____11957 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____11957 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11959 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____11987 ->
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
            | uu____12000 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____12012 =
      let uu____12016 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____12016
        (FStar_List.map
           (fun u  ->
              let uu____12028 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____12028 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____12012 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____12056 = FStar_Util.set_is_empty x  in
      if uu____12056
      then []
      else
        (let s =
           let uu____12074 =
             let uu____12077 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____12077  in
           FStar_All.pipe_right uu____12074 FStar_Util.set_elements  in
         (let uu____12093 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____12093
          then
            let uu____12098 =
              let uu____12100 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____12100  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____12098
          else ());
         (let r =
            let uu____12109 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____12109  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____12148 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____12148
                     then
                       let uu____12153 =
                         let uu____12155 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____12155
                          in
                       let uu____12159 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____12161 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____12153 uu____12159 uu____12161
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
        let uu____12191 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____12191 FStar_Util.set_elements  in
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
        | ([],uu____12230) -> generalized_univ_names
        | (uu____12237,[]) -> explicit_univ_names
        | uu____12244 ->
            let uu____12253 =
              let uu____12259 =
                let uu____12261 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____12261
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____12259)
               in
            FStar_Errors.raise_error uu____12253 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____12283 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____12283
       then
         let uu____12288 = FStar_Syntax_Print.term_to_string t  in
         let uu____12290 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____12288 uu____12290
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____12299 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____12299
        then
          let uu____12304 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____12304
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____12313 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____12313
         then
           let uu____12318 = FStar_Syntax_Print.term_to_string t  in
           let uu____12320 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____12318 uu____12320
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
        let uu____12404 =
          let uu____12406 =
            FStar_Util.for_all
              (fun uu____12420  ->
                 match uu____12420 with
                 | (uu____12430,uu____12431,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____12406  in
        if uu____12404
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____12483 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____12483
              then
                let uu____12486 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____12486
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____12493 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____12493
               then
                 let uu____12496 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____12496
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____12514 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____12514 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____12548 =
             match uu____12548 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____12585 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____12585
                   then
                     let uu____12590 =
                       let uu____12592 =
                         let uu____12596 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____12596
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____12592
                         (FStar_String.concat ", ")
                        in
                     let uu____12644 =
                       let uu____12646 =
                         let uu____12650 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____12650
                           (FStar_List.map
                              (fun u  ->
                                 let uu____12663 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____12665 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____12663
                                   uu____12665))
                          in
                       FStar_All.pipe_right uu____12646
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____12590
                       uu____12644
                   else ());
                  (let univs2 =
                     let uu____12679 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____12691 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____12691) univs1
                       uu____12679
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____12698 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____12698
                    then
                      let uu____12703 =
                        let uu____12705 =
                          let uu____12709 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____12709
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____12705
                          (FStar_String.concat ", ")
                         in
                      let uu____12757 =
                        let uu____12759 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____12773 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____12775 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____12773
                                    uu____12775))
                           in
                        FStar_All.pipe_right uu____12759
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____12703 uu____12757
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____12796 =
             let uu____12813 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____12813  in
           match uu____12796 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____12903 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____12903
                 then ()
                 else
                   (let uu____12908 = lec_hd  in
                    match uu____12908 with
                    | (lb1,uu____12916,uu____12917) ->
                        let uu____12918 = lec2  in
                        (match uu____12918 with
                         | (lb2,uu____12926,uu____12927) ->
                             let msg =
                               let uu____12930 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____12932 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____12930 uu____12932
                                in
                             let uu____12935 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____12935))
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
                 let uu____13003 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____13003
                 then ()
                 else
                   (let uu____13008 = lec_hd  in
                    match uu____13008 with
                    | (lb1,uu____13016,uu____13017) ->
                        let uu____13018 = lec2  in
                        (match uu____13018 with
                         | (lb2,uu____13026,uu____13027) ->
                             let msg =
                               let uu____13030 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____13032 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____13030 uu____13032
                                in
                             let uu____13035 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____13035))
                  in
               let lecs1 =
                 let uu____13046 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____13099 = univs_and_uvars_of_lec this_lec  in
                        match uu____13099 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____13046 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____13204 = lec_hd  in
                   match uu____13204 with
                   | (lbname,e,c) ->
                       let uu____13214 =
                         let uu____13220 =
                           let uu____13222 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____13224 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____13226 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____13222 uu____13224 uu____13226
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____13220)
                          in
                       let uu____13230 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____13214 uu____13230
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____13249 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____13249 with
                         | FStar_Pervasives_Native.Some uu____13258 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____13266 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____13270 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____13270 with
                              | (bs,kres) ->
                                  ((let uu____13314 =
                                      let uu____13315 =
                                        let uu____13318 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____13318
                                         in
                                      uu____13315.FStar_Syntax_Syntax.n  in
                                    match uu____13314 with
                                    | FStar_Syntax_Syntax.Tm_type uu____13319
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____13323 =
                                          let uu____13325 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____13325  in
                                        if uu____13323
                                        then fail1 kres
                                        else ()
                                    | uu____13330 -> fail1 kres);
                                   (let a =
                                      let uu____13332 =
                                        let uu____13335 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _13338  ->
                                             FStar_Pervasives_Native.Some
                                               _13338) uu____13335
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____13332
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____13346 ->
                                          let uu____13355 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____13355
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
                      (fun uu____13458  ->
                         match uu____13458 with
                         | (lbname,e,c) ->
                             let uu____13504 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____13565 ->
                                   let uu____13578 = (e, c)  in
                                   (match uu____13578 with
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
                                                (fun uu____13618  ->
                                                   match uu____13618 with
                                                   | (x,uu____13624) ->
                                                       let uu____13625 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____13625)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____13643 =
                                                let uu____13645 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____13645
                                                 in
                                              if uu____13643
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
                                          let uu____13654 =
                                            let uu____13655 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____13655.FStar_Syntax_Syntax.n
                                             in
                                          match uu____13654 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____13680 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____13680 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____13691 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____13695 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____13695, gen_tvars))
                                in
                             (match uu____13504 with
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
        (let uu____13842 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____13842
         then
           let uu____13845 =
             let uu____13847 =
               FStar_List.map
                 (fun uu____13862  ->
                    match uu____13862 with
                    | (lb,uu____13871,uu____13872) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____13847 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____13845
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____13898  ->
                match uu____13898 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____13927 = gen env is_rec lecs  in
           match uu____13927 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____14026  ->
                       match uu____14026 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____14088 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____14088
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____14136  ->
                           match uu____14136 with
                           | (l,us,e,c,gvs) ->
                               let uu____14170 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____14172 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____14174 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____14176 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____14178 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____14170 uu____14172 uu____14174
                                 uu____14176 uu____14178))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____14223  ->
                match uu____14223 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____14267 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____14267, t, c, gvs)) univnames_lecs
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
              (let uu____14332 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____14332 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____14338 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _14341  -> FStar_Pervasives_Native.Some _14341)
                     uu____14338)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1675_14361 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1675_14361.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1675_14361.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____14362 -> e2  in
          let uu____14363 = maybe_coerce_lc env1 e lc t2  in
          match uu____14363 with
          | (e1,lc1) ->
              let uu____14376 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____14376 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14385 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____14391 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____14385 uu____14391
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____14400 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____14400
                     then
                       let uu____14405 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____14405
                     else ());
                    (let uu____14411 = decorate e1 t2  in
                     (uu____14411, lc1, g))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____14439 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____14439
         then
           let uu____14442 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____14442
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____14456 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____14456 with
         | (c,g_c) ->
             let uu____14468 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____14468
             then
               let uu____14476 =
                 let uu____14478 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____14478  in
               (uu____14476, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____14486 =
                    let uu____14487 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____14487
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____14486
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____14488 = check_trivial_precondition env c1  in
                match uu____14488 with
                | (ct,vc,g_pre) ->
                    ((let uu____14504 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____14504
                      then
                        let uu____14509 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____14509
                      else ());
                     (let uu____14514 =
                        let uu____14516 =
                          let uu____14517 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____14517  in
                        discharge uu____14516  in
                      let uu____14518 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____14514, uu____14518)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_14552 =
        match uu___8_14552 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____14562)::[] -> f fst1
        | uu____14587 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____14599 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____14599
          (fun _14600  -> FStar_TypeChecker_Common.NonTrivial _14600)
         in
      let op_or_e e =
        let uu____14611 =
          let uu____14612 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____14612  in
        FStar_All.pipe_right uu____14611
          (fun _14615  -> FStar_TypeChecker_Common.NonTrivial _14615)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _14622  -> FStar_TypeChecker_Common.NonTrivial _14622)
         in
      let op_or_t t =
        let uu____14633 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____14633
          (fun _14636  -> FStar_TypeChecker_Common.NonTrivial _14636)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _14643  -> FStar_TypeChecker_Common.NonTrivial _14643)
         in
      let short_op_ite uu___9_14649 =
        match uu___9_14649 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____14659)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____14686)::[] ->
            let uu____14727 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____14727
              (fun _14728  -> FStar_TypeChecker_Common.NonTrivial _14728)
        | uu____14729 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____14741 =
          let uu____14749 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____14749)  in
        let uu____14757 =
          let uu____14767 =
            let uu____14775 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____14775)  in
          let uu____14783 =
            let uu____14793 =
              let uu____14801 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____14801)  in
            let uu____14809 =
              let uu____14819 =
                let uu____14827 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____14827)  in
              let uu____14835 =
                let uu____14845 =
                  let uu____14853 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____14853)  in
                [uu____14845; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____14819 :: uu____14835  in
            uu____14793 :: uu____14809  in
          uu____14767 :: uu____14783  in
        uu____14741 :: uu____14757  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____14915 =
            FStar_Util.find_map table
              (fun uu____14930  ->
                 match uu____14930 with
                 | (x,mk1) ->
                     let uu____14947 = FStar_Ident.lid_equals x lid  in
                     if uu____14947
                     then
                       let uu____14952 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____14952
                     else FStar_Pervasives_Native.None)
             in
          (match uu____14915 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____14956 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____14964 =
      let uu____14965 = FStar_Syntax_Util.un_uinst l  in
      uu____14965.FStar_Syntax_Syntax.n  in
    match uu____14964 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____14970 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____15006)::uu____15007 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____15026 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____15035,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____15036))::uu____15037 -> bs
      | uu____15055 ->
          let uu____15056 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____15056 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____15060 =
                 let uu____15061 = FStar_Syntax_Subst.compress t  in
                 uu____15061.FStar_Syntax_Syntax.n  in
               (match uu____15060 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____15065) ->
                    let uu____15086 =
                      FStar_Util.prefix_until
                        (fun uu___10_15126  ->
                           match uu___10_15126 with
                           | (uu____15134,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____15135)) ->
                               false
                           | uu____15140 -> true) bs'
                       in
                    (match uu____15086 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____15176,uu____15177) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____15249,uu____15250) ->
                         let uu____15323 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____15343  ->
                                   match uu____15343 with
                                   | (x,uu____15352) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____15323
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____15401  ->
                                     match uu____15401 with
                                     | (x,i) ->
                                         let uu____15420 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____15420, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____15431 -> bs))
  
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
            let uu____15460 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____15460
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
          let uu____15491 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____15491
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
        (let uu____15534 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____15534
         then
           ((let uu____15539 = FStar_Ident.text_of_lid lident  in
             d uu____15539);
            (let uu____15541 = FStar_Ident.text_of_lid lident  in
             let uu____15543 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____15541 uu____15543))
         else ());
        (let fv =
           let uu____15549 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____15549
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
         let uu____15561 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1835_15563 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1835_15563.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1835_15563.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1835_15563.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1835_15563.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___1835_15563.FStar_Syntax_Syntax.sigopts)
           }), uu____15561))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_15581 =
        match uu___11_15581 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____15584 -> false  in
      let reducibility uu___12_15592 =
        match uu___12_15592 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____15599 -> false  in
      let assumption uu___13_15607 =
        match uu___13_15607 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____15611 -> false  in
      let reification uu___14_15619 =
        match uu___14_15619 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____15622 -> true
        | uu____15624 -> false  in
      let inferred uu___15_15632 =
        match uu___15_15632 with
        | FStar_Syntax_Syntax.Discriminator uu____15634 -> true
        | FStar_Syntax_Syntax.Projector uu____15636 -> true
        | FStar_Syntax_Syntax.RecordType uu____15642 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____15652 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____15665 -> false  in
      let has_eq uu___16_15673 =
        match uu___16_15673 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____15677 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____15756 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____15763 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____15796 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____15796))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____15827 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____15827
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
           | FStar_Syntax_Syntax.Sig_bundle uu____15847 ->
               let uu____15856 =
                 let uu____15858 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_15864  ->
                           match uu___17_15864 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____15867 -> false))
                    in
                 Prims.op_Negation uu____15858  in
               if uu____15856
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____15874 -> ()
           | uu____15881 ->
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
      let uu____15895 =
        let uu____15897 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_15903  ->
                  match uu___18_15903 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____15906 -> false))
           in
        FStar_All.pipe_right uu____15897 Prims.op_Negation  in
      if uu____15895
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____15927 =
            let uu____15933 =
              let uu____15935 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____15935 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____15933)  in
          FStar_Errors.raise_error uu____15927 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____15953 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____15961 =
            let uu____15963 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____15963  in
          if uu____15961 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____15974),uu____15975) ->
              ((let uu____15987 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____15987
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____15996 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____15996
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____16007 ->
              ((let uu____16017 =
                  let uu____16019 =
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
                  Prims.op_Negation uu____16019  in
                if uu____16017 then err'1 () else ());
               (let uu____16029 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_16035  ->
                           match uu___19_16035 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____16038 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____16029
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____16044 ->
              let uu____16051 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____16051 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____16059 ->
              let uu____16066 =
                let uu____16068 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____16068  in
              if uu____16066 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____16078 ->
              let uu____16079 =
                let uu____16081 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____16081  in
              if uu____16079 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16091 ->
              let uu____16104 =
                let uu____16106 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____16106  in
              if uu____16104 then err'1 () else ()
          | uu____16116 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____16155 =
          let uu____16156 = FStar_Syntax_Subst.compress t1  in
          uu____16156.FStar_Syntax_Syntax.n  in
        match uu____16155 with
        | FStar_Syntax_Syntax.Tm_arrow uu____16160 ->
            let uu____16175 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____16175 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____16208;
               FStar_Syntax_Syntax.index = uu____16209;
               FStar_Syntax_Syntax.sort = t2;_},uu____16211)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____16220) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____16246) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____16252 -> false
      
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
        (let uu____16262 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____16262
         then
           let uu____16267 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____16267
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
                  let uu____16332 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____16332 r  in
                let uu____16342 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____16342 with
                | (uu____16351,signature) ->
                    let uu____16353 =
                      let uu____16354 = FStar_Syntax_Subst.compress signature
                         in
                      uu____16354.FStar_Syntax_Syntax.n  in
                    (match uu____16353 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16362) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____16410 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____16425 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____16427 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____16425 eff_name.FStar_Ident.str
                                       uu____16427) r
                                 in
                              (match uu____16410 with
                               | (is,g) ->
                                   let uu____16440 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____16442 =
                                             let uu____16443 =
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
                                                 = uu____16443;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____16442
                                            in
                                         let uu____16462 =
                                           let uu____16469 =
                                             let uu____16470 =
                                               let uu____16485 =
                                                 let uu____16494 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____16494]  in
                                               (uu____16485, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____16470
                                              in
                                           FStar_Syntax_Syntax.mk uu____16469
                                            in
                                         uu____16462
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____16525 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____16525
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____16534 =
                                           let uu____16539 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____16539
                                            in
                                         uu____16534
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____16440, g))
                          | uu____16548 -> fail1 signature)
                     | uu____16549 -> fail1 signature)
  
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
            let uu____16580 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____16580
              (fun ed  ->
                 let uu____16588 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____16588 u a_tm)
  
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
              let uu____16624 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____16624 with
              | (uu____16629,sig_tm) ->
                  let fail1 t =
                    let uu____16637 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____16637 r  in
                  let uu____16643 =
                    let uu____16644 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____16644.FStar_Syntax_Syntax.n  in
                  (match uu____16643 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16648) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____16671)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____16693 -> fail1 sig_tm)
                   | uu____16694 -> fail1 sig_tm)
  
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
          (let uu____16725 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____16725
           then
             let uu____16730 = FStar_Syntax_Print.comp_to_string c  in
             let uu____16732 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____16730 uu____16732
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered1 =
             let err uu____16762 =
               let uu____16763 =
                 let uu____16769 =
                   let uu____16771 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____16773 = FStar_Util.string_of_bool is_layered1
                      in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____16771 uu____16773
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____16769)  in
               FStar_Errors.raise_error uu____16763 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered1
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____16785,uu____16786::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____16854 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____16859,c1) ->
                    let uu____16881 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____16881
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____16916 -> err ())
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____16918 =
             let uu____16929 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____16930 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____16929, (ct.FStar_Syntax_Syntax.result_typ), uu____16930)
              in
           match uu____16918 with
           | (u,a,c_is) ->
               let uu____16978 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____16978 with
                | (uu____16987,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____16998 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____17000 = FStar_Ident.string_of_lid tgt  in
                      let uu____17002 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____16998 uu____17000 s uu____17002
                       in
                    let uu____17005 =
                      let uu____17038 =
                        let uu____17039 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____17039.FStar_Syntax_Syntax.n  in
                      match uu____17038 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____17103 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____17103 with
                           | (a_b::bs1,c2) ->
                               let uu____17163 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____17225 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____17163, uu____17225))
                      | uu____17252 ->
                          let uu____17253 =
                            let uu____17259 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____17259)
                             in
                          FStar_Errors.raise_error uu____17253 r
                       in
                    (match uu____17005 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____17377 =
                           let uu____17384 =
                             let uu____17385 =
                               let uu____17386 =
                                 let uu____17393 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____17393, a)  in
                               FStar_Syntax_Syntax.NT uu____17386  in
                             [uu____17385]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____17384
                             (fun b  ->
                                let uu____17410 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____17412 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____17414 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____17416 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____17410 uu____17412 uu____17414
                                  uu____17416) r
                            in
                         (match uu____17377 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____17430 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____17430
                                then
                                  let uu____17435 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____17444 =
                                             let uu____17446 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____17446
                                              in
                                           Prims.op_Hat s uu____17444) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____17435
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____17477 =
                                           let uu____17484 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____17484, t)  in
                                         FStar_Syntax_Syntax.NT uu____17477)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____17503 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____17503
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____17509 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____17509
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____17518 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____17518)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____17522 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____17522
                                   in
                                let c1 =
                                  let uu____17525 =
                                    let uu____17526 =
                                      let uu____17537 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____17537
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____17526;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____17525  in
                                (let uu____17557 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____17557
                                 then
                                   let uu____17562 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____17562
                                 else ());
                                (let uu____17567 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____17567))))))))
  
let lift_tf_layered_effect_term :
  'Auu____17581 .
    'Auu____17581 ->
      FStar_Syntax_Syntax.sub_eff ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun sub1  ->
      fun u  ->
        fun a  ->
          fun e  ->
            let lift =
              let uu____17610 =
                let uu____17615 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____17615
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____17610 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____17658 =
                let uu____17659 =
                  let uu____17662 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____17662
                    FStar_Syntax_Subst.compress
                   in
                uu____17659.FStar_Syntax_Syntax.n  in
              match uu____17658 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____17685::bs,uu____17687)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____17727 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____17727
                    FStar_Pervasives_Native.fst
              | uu____17833 ->
                  let uu____17834 =
                    let uu____17840 =
                      let uu____17842 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____17842
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____17840)  in
                  FStar_Errors.raise_error uu____17834
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____17869 = FStar_Syntax_Syntax.as_arg a  in
              let uu____17878 =
                let uu____17889 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____17925  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____17932 =
                  let uu____17943 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____17943]  in
                FStar_List.append uu____17889 uu____17932  in
              uu____17869 :: uu____17878  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____18007 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____18007
      then
        let uu____18010 =
          let uu____18023 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____18023
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____18010;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18058 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____18058 with
           | (uu____18067,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____18086 =
                 let uu____18087 =
                   let uu___2197_18088 = ct  in
                   let uu____18089 =
                     let uu____18100 =
                       let uu____18109 =
                         let uu____18110 =
                           let uu____18117 =
                             let uu____18118 =
                               let uu____18135 =
                                 let uu____18146 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____18146; wp]  in
                               (lift_t, uu____18135)  in
                             FStar_Syntax_Syntax.Tm_app uu____18118  in
                           FStar_Syntax_Syntax.mk uu____18117  in
                         uu____18110 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____18109
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____18100]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2197_18088.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2197_18088.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____18089;
                     FStar_Syntax_Syntax.flags =
                       (uu___2197_18088.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____18087  in
               (uu____18086, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____18246 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____18246 with
           | (uu____18253,lift_t) ->
               let uu____18255 =
                 let uu____18262 =
                   let uu____18263 =
                     let uu____18280 =
                       let uu____18291 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____18300 =
                         let uu____18311 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____18320 =
                           let uu____18331 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____18331]  in
                         uu____18311 :: uu____18320  in
                       uu____18291 :: uu____18300  in
                     (lift_t, uu____18280)  in
                   FStar_Syntax_Syntax.Tm_app uu____18263  in
                 FStar_Syntax_Syntax.mk uu____18262  in
               uu____18255 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____18384 =
           let uu____18397 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____18397 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____18384;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____18433  ->
                        fun uu____18434  -> fun e  -> FStar_Util.return_all e))
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
        let uu____18464 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____18464 with
        | (uu____18469,t) ->
            let err n1 =
              let uu____18479 =
                let uu____18485 =
                  let uu____18487 = FStar_Ident.string_of_lid datacon  in
                  let uu____18489 = FStar_Util.string_of_int n1  in
                  let uu____18491 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____18487 uu____18489 uu____18491
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____18485)
                 in
              let uu____18495 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____18479 uu____18495  in
            let uu____18496 =
              let uu____18497 = FStar_Syntax_Subst.compress t  in
              uu____18497.FStar_Syntax_Syntax.n  in
            (match uu____18496 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18501) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____18556  ->
                           match uu____18556 with
                           | (uu____18564,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____18573 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____18605 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____18605
                      FStar_Pervasives_Native.fst)
             | uu____18616 -> err Prims.int_zero)
  