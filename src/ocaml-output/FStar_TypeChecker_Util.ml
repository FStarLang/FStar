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
                let uu____1649 =
                  FStar_Syntax_Util.get_match_with_close_wps
                    md.FStar_Syntax_Syntax.match_wps
                   in
                match uu____1649 with
                | (uu____1658,uu____1659,close1) ->
                    FStar_List.fold_right
                      (fun x  ->
                         fun wp  ->
                           let bs =
                             let uu____1682 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____1682]  in
                           let us =
                             let uu____1704 =
                               let uu____1707 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               [uu____1707]  in
                             u_res :: uu____1704  in
                           let wp1 =
                             FStar_Syntax_Util.abs bs wp
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None
                                     [FStar_Syntax_Syntax.TOTAL]))
                              in
                           let uu____1713 =
                             let uu____1718 =
                               FStar_TypeChecker_Env.inst_effect_fun_with us
                                 env md close1
                                in
                             let uu____1719 =
                               let uu____1720 =
                                 FStar_Syntax_Syntax.as_arg res_t  in
                               let uu____1729 =
                                 let uu____1740 =
                                   FStar_Syntax_Syntax.as_arg
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____1749 =
                                   let uu____1760 =
                                     FStar_Syntax_Syntax.as_arg wp1  in
                                   [uu____1760]  in
                                 uu____1740 :: uu____1749  in
                               uu____1720 :: uu____1729  in
                             FStar_Syntax_Syntax.mk_Tm_app uu____1718
                               uu____1719
                              in
                           uu____1713 FStar_Pervasives_Native.None
                             wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1802 = destruct_wp_comp c1  in
              match uu____1802 with
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
                let uu____1842 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____1842
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
                  let uu____1892 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____1892
                    (close_guard_implicits env false bs)))
  
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
              ({ FStar_Syntax_Syntax.ppname = uu____1916;
                 FStar_Syntax_Syntax.index = uu____1917;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____1919;
                     FStar_Syntax_Syntax.vars = uu____1920;_};_},uu____1921)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_wp_comp env [x] c
          | uu____1929 -> c
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_1941  ->
            match uu___0_1941 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1944 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____1969 =
            let uu____1972 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____1972 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____1969
            (fun c  ->
               (let uu____2028 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2028) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2032 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2032)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2043 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2043 with
                | (head1,uu____2060) ->
                    let uu____2081 =
                      let uu____2082 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2082.FStar_Syntax_Syntax.n  in
                    (match uu____2081 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2087 =
                           let uu____2089 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2089
                            in
                         Prims.op_Negation uu____2087
                     | uu____2090 -> true)))
              &&
              (let uu____2093 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2093)
  
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
            let uu____2121 =
              let uu____2123 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2123  in
            if uu____2121
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2130 = FStar_Syntax_Util.is_unit t  in
               if uu____2130
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
                    let uu____2139 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2139
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2144 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2144 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2154 =
                             let uu____2155 =
                               let uu____2160 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2161 =
                                 let uu____2162 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2171 =
                                   let uu____2182 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2182]  in
                                 uu____2162 :: uu____2171  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2160
                                 uu____2161
                                in
                             uu____2155 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2154)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2216 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2216
           then
             let uu____2221 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2223 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2225 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2221 uu____2223 uu____2225
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
                (let uu____2283 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____2283
                 then
                   let uu____2288 =
                     let uu____2290 = FStar_Syntax_Syntax.mk_Comp ct1  in
                     FStar_Syntax_Print.comp_to_string uu____2290  in
                   let uu____2291 =
                     let uu____2293 = FStar_Syntax_Syntax.mk_Comp ct2  in
                     FStar_Syntax_Print.comp_to_string uu____2293  in
                   FStar_Util.print2 "Binding c1:%s and c2:%s {\n" uu____2288
                     uu____2291
                 else ());
                (let ed = FStar_TypeChecker_Env.get_effect_decl env m  in
                 let uu____2298 =
                   let uu____2309 =
                     FStar_List.hd ct1.FStar_Syntax_Syntax.comp_univs  in
                   let uu____2310 =
                     FStar_List.map FStar_Pervasives_Native.fst
                       ct1.FStar_Syntax_Syntax.effect_args
                      in
                   (uu____2309, (ct1.FStar_Syntax_Syntax.result_typ),
                     uu____2310)
                    in
                 match uu____2298 with
                 | (u1,t1,is1) ->
                     let uu____2344 =
                       let uu____2355 =
                         FStar_List.hd ct2.FStar_Syntax_Syntax.comp_univs  in
                       let uu____2356 =
                         FStar_List.map FStar_Pervasives_Native.fst
                           ct2.FStar_Syntax_Syntax.effect_args
                          in
                       (uu____2355, (ct2.FStar_Syntax_Syntax.result_typ),
                         uu____2356)
                        in
                     (match uu____2344 with
                      | (u2,t2,is2) ->
                          let uu____2390 =
                            FStar_TypeChecker_Env.inst_tscheme_with
                              ed.FStar_Syntax_Syntax.bind_wp [u1; u2]
                             in
                          (match uu____2390 with
                           | (uu____2399,bind_t) ->
                               let bind_t_shape_error s =
                                 let uu____2414 =
                                   let uu____2416 =
                                     FStar_Syntax_Print.term_to_string bind_t
                                      in
                                   FStar_Util.format2
                                     "bind %s does not have proper shape (reason:%s)"
                                     uu____2416 s
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____2414)
                                  in
                               let uu____2420 =
                                 let uu____2465 =
                                   let uu____2466 =
                                     FStar_Syntax_Subst.compress bind_t  in
                                   uu____2466.FStar_Syntax_Syntax.n  in
                                 match uu____2465 with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____2542 =
                                       FStar_Syntax_Subst.open_comp bs c  in
                                     (match uu____2542 with
                                      | (a_b::b_b::bs1,c1) ->
                                          let uu____2627 =
                                            let uu____2654 =
                                              FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   (Prims.of_int (2))) bs1
                                               in
                                            FStar_All.pipe_right uu____2654
                                              (fun uu____2739  ->
                                                 match uu____2739 with
                                                 | (l1,l2) ->
                                                     let uu____2820 =
                                                       FStar_List.hd l2  in
                                                     let uu____2833 =
                                                       let uu____2840 =
                                                         FStar_List.tl l2  in
                                                       FStar_List.hd
                                                         uu____2840
                                                        in
                                                     (l1, uu____2820,
                                                       uu____2833))
                                             in
                                          (match uu____2627 with
                                           | (rest_bs,f_b,g_b) ->
                                               let uu____2968 =
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                   c1
                                                  in
                                               (a_b, b_b, rest_bs, f_b, g_b,
                                                 uu____2968)))
                                 | uu____3001 ->
                                     let uu____3002 =
                                       bind_t_shape_error
                                         "Either not an arrow or not enough binders"
                                        in
                                     FStar_Errors.raise_error uu____3002 r1
                                  in
                               (match uu____2420 with
                                | (a_b,b_b,rest_bs,f_b,g_b,bind_ct) ->
                                    let uu____3127 =
                                      let uu____3134 =
                                        let uu____3135 =
                                          let uu____3136 =
                                            let uu____3143 =
                                              FStar_All.pipe_right a_b
                                                FStar_Pervasives_Native.fst
                                               in
                                            (uu____3143, t1)  in
                                          FStar_Syntax_Syntax.NT uu____3136
                                           in
                                        let uu____3154 =
                                          let uu____3157 =
                                            let uu____3158 =
                                              let uu____3165 =
                                                FStar_All.pipe_right b_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____3165, t2)  in
                                            FStar_Syntax_Syntax.NT uu____3158
                                             in
                                          [uu____3157]  in
                                        uu____3135 :: uu____3154  in
                                      FStar_TypeChecker_Env.uvars_for_binders
                                        env rest_bs uu____3134
                                        (fun b1  ->
                                           let uu____3180 =
                                             FStar_Syntax_Print.binder_to_string
                                               b1
                                              in
                                           let uu____3182 =
                                             FStar_Range.string_of_range r1
                                              in
                                           FStar_Util.format3
                                             "implicit var for binder %s of %s:bind at %s"
                                             uu____3180
                                             (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             uu____3182) r1
                                       in
                                    (match uu____3127 with
                                     | (rest_bs_uvars,g_uvars) ->
                                         let subst1 =
                                           FStar_List.map2
                                             (fun b1  ->
                                                fun t  ->
                                                  let uu____3219 =
                                                    let uu____3226 =
                                                      FStar_All.pipe_right b1
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    (uu____3226, t)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3219) (a_b :: b_b
                                             :: rest_bs) (t1 :: t2 ::
                                             rest_bs_uvars)
                                            in
                                         let f_guard =
                                           let f_sort_is =
                                             let uu____3253 =
                                               let uu____3254 =
                                                 let uu____3257 =
                                                   let uu____3258 =
                                                     FStar_All.pipe_right f_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3258.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3257
                                                  in
                                               uu____3254.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3253 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____3269,uu____3270::is)
                                                 ->
                                                 let uu____3312 =
                                                   FStar_All.pipe_right is
                                                     (FStar_List.map
                                                        FStar_Pervasives_Native.fst)
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3312
                                                   (FStar_List.map
                                                      (FStar_Syntax_Subst.subst
                                                         subst1))
                                             | uu____3345 ->
                                                 let uu____3346 =
                                                   bind_t_shape_error
                                                     "f's type is not a repr type"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3346 r1
                                              in
                                           FStar_List.fold_left2
                                             (fun g  ->
                                                fun i1  ->
                                                  fun f_i1  ->
                                                    let uu____3362 =
                                                      FStar_TypeChecker_Rel.teq
                                                        env i1 f_i1
                                                       in
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g uu____3362)
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
                                             let uu____3381 =
                                               let uu____3382 =
                                                 let uu____3385 =
                                                   let uu____3386 =
                                                     FStar_All.pipe_right g_b
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   uu____3386.FStar_Syntax_Syntax.sort
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____3385
                                                  in
                                               uu____3382.FStar_Syntax_Syntax.n
                                                in
                                             match uu____3381 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs,c) ->
                                                 let uu____3419 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c
                                                    in
                                                 (match uu____3419 with
                                                  | (bs1,c1) ->
                                                      let bs_subst =
                                                        let uu____3429 =
                                                          let uu____3436 =
                                                            let uu____3437 =
                                                              FStar_List.hd
                                                                bs1
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3437
                                                              FStar_Pervasives_Native.fst
                                                             in
                                                          let uu____3458 =
                                                            let uu____3461 =
                                                              FStar_All.pipe_right
                                                                x_a
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3461
                                                              FStar_Syntax_Syntax.bv_to_name
                                                             in
                                                          (uu____3436,
                                                            uu____3458)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____3429
                                                         in
                                                      let c2 =
                                                        FStar_Syntax_Subst.subst_comp
                                                          [bs_subst] c1
                                                         in
                                                      let uu____3475 =
                                                        let uu____3476 =
                                                          FStar_Syntax_Subst.compress
                                                            (FStar_Syntax_Util.comp_result
                                                               c2)
                                                           in
                                                        uu____3476.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____3475 with
                                                       | FStar_Syntax_Syntax.Tm_app
                                                           (uu____3481,uu____3482::is)
                                                           ->
                                                           let uu____3524 =
                                                             FStar_All.pipe_right
                                                               is
                                                               (FStar_List.map
                                                                  FStar_Pervasives_Native.fst)
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____3524
                                                             (FStar_List.map
                                                                (FStar_Syntax_Subst.subst
                                                                   subst1))
                                                       | uu____3557 ->
                                                           let uu____3558 =
                                                             bind_t_shape_error
                                                               "g's type is not a repr type"
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____3558 r1))
                                             | uu____3567 ->
                                                 let uu____3568 =
                                                   bind_t_shape_error
                                                     "g's type is not an arrow"
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____3568 r1
                                              in
                                           let env_g =
                                             FStar_TypeChecker_Env.push_binders
                                               env [x_a]
                                              in
                                           let uu____3590 =
                                             FStar_List.fold_left2
                                               (fun g  ->
                                                  fun i1  ->
                                                    fun g_i1  ->
                                                      let uu____3598 =
                                                        FStar_TypeChecker_Rel.teq
                                                          env_g i1 g_i1
                                                         in
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g uu____3598)
                                               FStar_TypeChecker_Env.trivial_guard
                                               is2 g_sort_is
                                              in
                                           FStar_All.pipe_right uu____3590
                                             (FStar_TypeChecker_Env.close_guard
                                                env [x_a])
                                            in
                                         let is =
                                           let uu____3614 =
                                             let uu____3615 =
                                               FStar_Syntax_Subst.compress
                                                 bind_ct.FStar_Syntax_Syntax.result_typ
                                                in
                                             uu____3615.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3614 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____3620,uu____3621::is) ->
                                               let uu____3663 =
                                                 FStar_All.pipe_right is
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3663
                                                 (FStar_List.map
                                                    (FStar_Syntax_Subst.subst
                                                       subst1))
                                           | uu____3696 ->
                                               let uu____3697 =
                                                 bind_t_shape_error
                                                   "return type is not a repr type"
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____3697 r1
                                            in
                                         let c =
                                           let uu____3707 =
                                             let uu____3708 =
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
                                                 = uu____3708;
                                               FStar_Syntax_Syntax.flags =
                                                 flags
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____3707
                                            in
                                         ((let uu____3728 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffects")
                                              in
                                           if uu____3728
                                           then
                                             let uu____3733 =
                                               FStar_Syntax_Print.comp_to_string
                                                 c
                                                in
                                             FStar_Util.print1
                                               "} c after bind: %s\n"
                                               uu____3733
                                           else ());
                                          (let uu____3738 =
                                             FStar_TypeChecker_Env.conj_guards
                                               [g_uvars; f_guard; g_guard]
                                              in
                                           (c, uu____3738))))))))
  
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
                let uu____3783 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____3809 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____3809 with
                  | (a,kwp) ->
                      let uu____3840 = destruct_wp_comp ct1  in
                      let uu____3847 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____3840, uu____3847)
                   in
                match uu____3783 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____3900 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____3900]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____3920 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3920]
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
                      let uu____3967 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____3976 =
                        let uu____3987 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____3996 =
                          let uu____4007 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____4016 =
                            let uu____4027 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____4036 =
                              let uu____4047 =
                                let uu____4056 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____4056  in
                              [uu____4047]  in
                            uu____4027 :: uu____4036  in
                          uu____4007 :: uu____4016  in
                        uu____3987 :: uu____3996  in
                      uu____3967 :: uu____3976  in
                    let wp =
                      let uu____4108 =
                        let uu____4113 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md
                            md.FStar_Syntax_Syntax.bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4113 wp_args  in
                      uu____4108 FStar_Pervasives_Native.None
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
              let uu____4161 = lift_comps env c1 c2 b true  in
              match uu____4161 with
              | (m,c11,c21,g_lift) ->
                  let uu____4179 =
                    let uu____4184 = FStar_Syntax_Util.comp_to_comp_typ c11
                       in
                    let uu____4185 = FStar_Syntax_Util.comp_to_comp_typ c21
                       in
                    (uu____4184, uu____4185)  in
                  (match uu____4179 with
                   | (ct1,ct2) ->
                       let uu____4192 =
                         let uu____4197 =
                           FStar_TypeChecker_Env.is_layered_effect env m  in
                         if uu____4197
                         then mk_layered_bind env m ct1 b ct2 flags r1
                         else
                           (let uu____4206 =
                              mk_non_layered_bind env m ct1 b ct2 flags r1
                               in
                            (uu____4206, FStar_TypeChecker_Env.trivial_guard))
                          in
                       (match uu____4192 with
                        | (c,g_bind) ->
                            let uu____4213 =
                              FStar_TypeChecker_Env.conj_guard g_lift g_bind
                               in
                            (c, uu____4213)))
  
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
            let uu____4249 =
              let uu____4250 =
                let uu____4261 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____4261]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4250;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4249  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____4306 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4312  ->
              match uu___1_4312 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4315 -> false))
       in
    if uu____4306
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4327  ->
              match uu___2_4327 with
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
        let uu____4355 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4355
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____4366 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____4366  in
           let pure_assume_wp1 =
             let uu____4371 = FStar_TypeChecker_Env.get_range env  in
             let uu____4372 =
               let uu____4377 =
                 let uu____4378 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____4378]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4377  in
             uu____4372 FStar_Pervasives_Native.None uu____4371  in
           let uu____4411 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____4411)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4439 =
          let uu____4440 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____4440 with
          | (c,g_c) ->
              let uu____4451 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4451
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____4465 = weaken_comp env c f1  in
                     (match uu____4465 with
                      | (c1,g_w) ->
                          let uu____4476 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____4476)))
           in
        let uu____4477 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____4477 weaken
  
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
                 let uu____4534 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____4534  in
               let pure_assert_wp1 =
                 let uu____4539 =
                   let uu____4544 =
                     let uu____4545 =
                       let uu____4554 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____4554
                        in
                     [uu____4545]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____4544
                    in
                 uu____4539 FStar_Pervasives_Native.None r  in
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
            let uu____4624 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____4624
            then (lc, g0)
            else
              (let flags =
                 let uu____4636 =
                   let uu____4644 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____4644
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4636 with
                 | (maybe_trivial_post,flags) ->
                     let uu____4674 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_4682  ->
                               match uu___3_4682 with
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
                               | uu____4685 -> []))
                        in
                     FStar_List.append flags uu____4674
                  in
               let strengthen uu____4695 =
                 let uu____4696 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____4696 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____4715 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____4715 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____4722 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4722
                              then
                                let uu____4726 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____4728 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____4726 uu____4728
                              else ());
                             (let uu____4733 =
                                strengthen_comp env reason c f flags  in
                              match uu____4733 with
                              | (c1,g_s) ->
                                  let uu____4744 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____4744))))
                  in
               let uu____4745 =
                 let uu____4746 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____4746
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____4745,
                 (let uu___580_4748 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___580_4748.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___580_4748.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___580_4748.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_4757  ->
            match uu___4_4757 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4761 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____4790 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4790
          then e
          else
            (let uu____4797 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4800 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4800)
                in
             if uu____4797
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
          fun uu____4853  ->
            match uu____4853 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4873 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____4873 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____4886 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____4886
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____4896 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____4896
                       then
                         let uu____4901 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____4901
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____4908 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____4908
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____4917 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____4917
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____4924 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____4924
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____4940 =
                  let uu____4941 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____4941
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____4949 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____4949, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____4952 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____4952 with
                     | (c1,g_c1) ->
                         let uu____4963 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____4963 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____4983  ->
                                    let uu____4984 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____4986 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____4991 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____4984 uu____4986 uu____4991);
                               (let aux uu____5009 =
                                  let uu____5010 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____5010
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5041
                                        ->
                                        let uu____5042 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5042
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5074 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5074
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____5119 =
                                  let uu____5120 =
                                    let uu____5122 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____5122  in
                                  if uu____5120
                                  then
                                    let uu____5136 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____5136
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5159 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5159))
                                  else
                                    (let uu____5174 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____5174
                                     then
                                       let close1 x reason c =
                                         let uu____5215 =
                                           let uu____5217 =
                                             let uu____5218 =
                                               FStar_All.pipe_right c
                                                 FStar_Syntax_Util.comp_effect_name
                                                in
                                             FStar_All.pipe_right uu____5218
                                               (FStar_TypeChecker_Env.norm_eff_name
                                                  env)
                                              in
                                           FStar_All.pipe_right uu____5217
                                             (FStar_TypeChecker_Env.is_layered_effect
                                                env)
                                            in
                                         if uu____5215
                                         then FStar_Util.Inl (c, reason)
                                         else
                                           (let x1 =
                                              let uu___651_5243 = x  in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___651_5243.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___651_5243.FStar_Syntax_Syntax.index);
                                                FStar_Syntax_Syntax.sort =
                                                  (FStar_Syntax_Util.comp_result
                                                     c1)
                                              }  in
                                            let uu____5244 =
                                              let uu____5250 =
                                                close_wp_comp_if_refinement_t
                                                  env
                                                  x1.FStar_Syntax_Syntax.sort
                                                  x1 c
                                                 in
                                              (uu____5250, reason)  in
                                            FStar_Util.Inl uu____5244)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____5286 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____5286
                                             (close1 x "c1 Tot")
                                       | (uu____5300,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____5323,uu____5324) -> aux ()
                                     else
                                       (let uu____5339 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____5339
                                        then
                                          let uu____5352 =
                                            let uu____5358 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____5358, "both GTot")  in
                                          FStar_Util.Inl uu____5352
                                        else aux ()))
                                   in
                                let uu____5369 = try_simplify ()  in
                                match uu____5369 with
                                | FStar_Util.Inl (c,reason) ->
                                    (debug1
                                       (fun uu____5399  ->
                                          let uu____5400 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____5400);
                                     (let uu____5403 =
                                        FStar_TypeChecker_Env.conj_guard g_c1
                                          g_c2
                                         in
                                      (c, uu____5403)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____5415  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____5441 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____5441 with
                                        | (c,g_bind) ->
                                            let uu____5452 =
                                              let uu____5453 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5453 g_bind
                                               in
                                            (c, uu____5452)
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
                                        let uu____5480 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5480 with
                                        | (m,uu____5492,lift2) ->
                                            let uu____5494 =
                                              lift_comp env c22 lift2  in
                                            (match uu____5494 with
                                             | (c23,g2) ->
                                                 let uu____5505 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____5505 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let vc1 =
                                                        let uu____5523 =
                                                          let uu____5528 =
                                                            let uu____5529 =
                                                              FStar_All.pipe_right
                                                                md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                                                FStar_Util.must
                                                               in
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              uu____5529
                                                             in
                                                          let uu____5532 =
                                                            let uu____5533 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5542 =
                                                              let uu____5553
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5553]
                                                               in
                                                            uu____5533 ::
                                                              uu____5542
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5528
                                                            uu____5532
                                                           in
                                                        uu____5523
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5586 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____5586 with
                                                       | (c,g_s) ->
                                                           let uu____5601 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____5601))))
                                         in
                                      let uu____5602 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5618 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____5618, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____5602 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____5634 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____5634
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____5643 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____5643
                                             then
                                               (debug1
                                                  (fun uu____5657  ->
                                                     let uu____5658 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____5660 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____5658 uu____5660);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____5668 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____5671 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____5671)
                                                   in
                                                if uu____5668
                                                then
                                                  let e1' =
                                                    let uu____5696 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____5696
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____5708  ->
                                                        let uu____5709 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____5711 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____5709
                                                          uu____5711);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____5726  ->
                                                        let uu____5727 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____5729 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____5727
                                                          uu____5729);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____5736 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____5736
                                                       in
                                                    let uu____5737 =
                                                      let uu____5742 =
                                                        let uu____5743 =
                                                          let uu____5744 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____5744]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____5743
                                                         in
                                                      weaken_comp uu____5742
                                                        c21 x_eq_e
                                                       in
                                                    match uu____5737 with
                                                    | (c22,g_w) ->
                                                        let uu____5769 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____5769
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____5780 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____5780))))))
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
      | uu____5797 -> g2
  
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
            (let uu____5821 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____5821)
           in
        let flags =
          if should_return1
          then
            let uu____5829 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____5829
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____5847 =
          let uu____5848 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5848 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____5861 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____5861
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____5869 =
                  let uu____5871 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____5871  in
                (if uu____5869
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___765_5880 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___765_5880.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___765_5880.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___765_5880.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____5881 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____5881, g_c)
                 else
                   (let uu____5884 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____5884, g_c)))
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
                   let uu____5895 =
                     let uu____5896 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____5896
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____5895
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____5899 =
                   let uu____5904 =
                     let uu____5905 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____5905
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____5904  in
                 match uu____5899 with
                 | (bind_c,g_bind) ->
                     let uu____5914 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____5915 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____5914, uu____5915))
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
            fun uu____5951  ->
              match uu____5951 with
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
                    let uu____5963 =
                      ((let uu____5967 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____5967) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____5963
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____5985 =
        let uu____5986 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____5986  in
      FStar_Syntax_Syntax.fvar uu____5985 FStar_Syntax_Syntax.delta_constant
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
                  let uu____6036 =
                    let uu____6041 =
                      let uu____6042 =
                        FStar_All.pipe_right ed.FStar_Syntax_Syntax.match_wps
                          FStar_Util.right
                         in
                      uu____6042.FStar_Syntax_Syntax.sif_then_else  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____6041 [u_a]
                     in
                  match uu____6036 with
                  | (uu____6051,conjunction) ->
                      let uu____6053 =
                        let uu____6062 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____6077 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____6062, uu____6077)  in
                      (match uu____6053 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____6123 =
                               let uu____6125 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____6125 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____6123)
                              in
                           let uu____6129 =
                             let uu____6174 =
                               let uu____6175 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____6175.FStar_Syntax_Syntax.n  in
                             match uu____6174 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____6224) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____6256 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____6256 with
                                  | (a_b::bs1,body1) ->
                                      let uu____6328 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____6328 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____6476 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____6476)))
                             | uu____6509 ->
                                 let uu____6510 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____6510 r
                              in
                           (match uu____6129 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____6635 =
                                  let uu____6642 =
                                    let uu____6643 =
                                      let uu____6644 =
                                        let uu____6651 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____6651, a)  in
                                      FStar_Syntax_Syntax.NT uu____6644  in
                                    [uu____6643]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____6642
                                    (fun b  ->
                                       let uu____6667 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____6669 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____6671 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____6667 uu____6669 uu____6671) r
                                   in
                                (match uu____6635 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____6709 =
                                                let uu____6716 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____6716, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____6709) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____6755 =
                                           let uu____6756 =
                                             let uu____6759 =
                                               let uu____6760 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____6760.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____6759
                                              in
                                           uu____6756.FStar_Syntax_Syntax.n
                                            in
                                         match uu____6755 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____6771,uu____6772::is) ->
                                             let uu____6814 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____6814
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____6847 ->
                                             let uu____6848 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____6848 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____6864 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____6864)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____6869 =
                                           let uu____6870 =
                                             let uu____6873 =
                                               let uu____6874 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____6874.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____6873
                                              in
                                           uu____6870.FStar_Syntax_Syntax.n
                                            in
                                         match uu____6869 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____6885,uu____6886::is) ->
                                             let uu____6928 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____6928
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____6961 ->
                                             let uu____6962 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____6962 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____6978 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____6978)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____6983 =
                                         let uu____6984 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____6984.FStar_Syntax_Syntax.n  in
                                       match uu____6983 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____6989,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____7044 ->
                                           let uu____7045 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____7045 r
                                        in
                                     let uu____7054 =
                                       let uu____7055 =
                                         let uu____7056 =
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
                                             uu____7056;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____7055
                                        in
                                     let uu____7079 =
                                       let uu____7080 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____7080 g_guard
                                        in
                                     (uu____7054, uu____7079))))
  
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
                fun uu____7125  ->
                  let uu____7130 =
                    FStar_Syntax_Util.get_match_with_close_wps
                      ed.FStar_Syntax_Syntax.match_wps
                     in
                  match uu____7130 with
                  | (if_then_else1,uu____7142,uu____7143) ->
                      let uu____7144 = destruct_wp_comp ct1  in
                      (match uu____7144 with
                       | (uu____7155,uu____7156,wp_t) ->
                           let uu____7158 = destruct_wp_comp ct2  in
                           (match uu____7158 with
                            | (uu____7169,uu____7170,wp_e) ->
                                let wp =
                                  let uu____7175 =
                                    FStar_Range.union_ranges
                                      wp_t.FStar_Syntax_Syntax.pos
                                      wp_e.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____7176 =
                                    let uu____7181 =
                                      FStar_TypeChecker_Env.inst_effect_fun_with
                                        [u_a] env ed if_then_else1
                                       in
                                    let uu____7182 =
                                      let uu____7183 =
                                        FStar_Syntax_Syntax.as_arg a  in
                                      let uu____7192 =
                                        let uu____7203 =
                                          FStar_Syntax_Syntax.as_arg p  in
                                        let uu____7212 =
                                          let uu____7223 =
                                            FStar_Syntax_Syntax.as_arg wp_t
                                             in
                                          let uu____7232 =
                                            let uu____7243 =
                                              FStar_Syntax_Syntax.as_arg wp_e
                                               in
                                            [uu____7243]  in
                                          uu____7223 :: uu____7232  in
                                        uu____7203 :: uu____7212  in
                                      uu____7183 :: uu____7192  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____7181
                                      uu____7182
                                     in
                                  uu____7176 FStar_Pervasives_Native.None
                                    uu____7175
                                   in
                                let uu____7292 = mk_comp ed u_a a wp []  in
                                (uu____7292,
                                  FStar_TypeChecker_Env.trivial_guard)))
  
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
               fun uu____7362  ->
                 match uu____7362 with
                 | (uu____7376,eff_label,uu____7378,uu____7379) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____7392 =
          let uu____7400 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____7438  ->
                    match uu____7438 with
                    | (uu____7453,uu____7454,flags,uu____7456) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_7473  ->
                                match uu___5_7473 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____7476 -> false))))
             in
          if uu____7400
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____7392 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____7513 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____7515 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____7515
              then
                let uu____7522 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____7522, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____7529 =
                       let uu____7538 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7538]  in
                     let uu____7557 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7529 uu____7557  in
                   let kwp =
                     let uu____7563 =
                       let uu____7572 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7572]  in
                     let uu____7591 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7563 uu____7591  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7598 =
                       let uu____7599 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7599]  in
                     let uu____7618 =
                       let uu____7621 =
                         let uu____7628 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7628
                          in
                       let uu____7629 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7621 uu____7629  in
                     FStar_Syntax_Util.abs uu____7598 uu____7618
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
                   let uu____7653 =
                     should_not_inline_whole_match ||
                       (let uu____7656 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7656)
                      in
                   if uu____7653 then cthen true else cthen false  in
                 let uu____7663 =
                   FStar_List.fold_right
                     (fun uu____7716  ->
                        fun uu____7717  ->
                          match (uu____7716, uu____7717) with
                          | ((g,eff_label,uu____7771,cthen),(uu____7773,celse,g_comp))
                              ->
                              let uu____7814 =
                                let uu____7819 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____7819
                                 in
                              (match uu____7814 with
                               | (cthen1,gthen) ->
                                   let uu____7830 =
                                     let uu____7839 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____7839 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____7862 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____7863 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____7862, uu____7863, g_lift)
                                      in
                                   (match uu____7830 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          if
                                            FStar_Pervasives_Native.fst
                                              md.FStar_Syntax_Syntax.is_layered
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____7947 =
                                          let uu____7952 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____7952
                                           in
                                        (match uu____7947 with
                                         | (c,g_conjunction) ->
                                             let uu____7963 =
                                               let uu____7964 =
                                                 let uu____7965 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____7965 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____7964 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____7963)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____7663 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____7999::[] -> (comp, g_comp)
                      | uu____8042 ->
                          let uu____8059 =
                            let uu____8061 =
                              let uu____8069 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              uu____8069.FStar_Syntax_Syntax.is_layered  in
                            FStar_Pervasives_Native.fst uu____8061  in
                          if uu____8059
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
                             let uu____8084 = destruct_wp_comp comp1  in
                             match uu____8084 with
                             | (uu____8095,uu____8096,wp) ->
                                 let uu____8098 =
                                   FStar_Syntax_Util.get_match_with_close_wps
                                     md1.FStar_Syntax_Syntax.match_wps
                                    in
                                 (match uu____8098 with
                                  | (uu____8109,ite_wp,uu____8111) ->
                                      let wp1 =
                                        let uu____8115 =
                                          let uu____8120 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [u_res_t] env md1 ite_wp
                                             in
                                          let uu____8121 =
                                            let uu____8122 =
                                              FStar_Syntax_Syntax.as_arg
                                                res_t
                                               in
                                            let uu____8131 =
                                              let uu____8142 =
                                                FStar_Syntax_Syntax.as_arg wp
                                                 in
                                              [uu____8142]  in
                                            uu____8122 :: uu____8131  in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            uu____8120 uu____8121
                                           in
                                        uu____8115
                                          FStar_Pervasives_Native.None
                                          wp.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____8175 =
                                        mk_comp md1 u_res_t res_t wp1
                                          bind_cases_flags
                                         in
                                      (uu____8175, g_comp)))))
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
          let uu____8209 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____8209 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____8225 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____8231 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____8225 uu____8231
              else
                (let uu____8240 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____8246 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____8240 uu____8246)
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
          let uu____8271 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____8271
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____8274 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____8274
        then u_res
        else
          (let is_total =
             let uu____8281 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____8281
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____8292 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____8292 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8295 =
                    let uu____8301 =
                      let uu____8303 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____8303
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____8301)
                     in
                  FStar_Errors.raise_error uu____8295
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
      let uu____8327 = destruct_wp_comp ct  in
      match uu____8327 with
      | (u_t,t,wp) ->
          let vc =
            let uu____8346 = FStar_TypeChecker_Env.get_range env  in
            let uu____8347 =
              let uu____8352 =
                let uu____8353 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____8353
                 in
              let uu____8356 =
                let uu____8357 = FStar_Syntax_Syntax.as_arg t  in
                let uu____8366 =
                  let uu____8377 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____8377]  in
                uu____8357 :: uu____8366  in
              FStar_Syntax_Syntax.mk_Tm_app uu____8352 uu____8356  in
            uu____8347 FStar_Pervasives_Native.None uu____8346  in
          let uu____8410 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____8410)
  
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
                  let uu____8465 = FStar_TypeChecker_Env.try_lookup_lid env f
                     in
                  match uu____8465 with
                  | FStar_Pervasives_Native.Some uu____8480 ->
                      ((let uu____8498 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____8498
                        then
                          let uu____8502 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____8502
                        else ());
                       (let coercion =
                          let uu____8508 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____8508
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____8515 =
                            let uu____8516 =
                              let uu____8517 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____8517
                               in
                            (FStar_Pervasives_Native.None, uu____8516)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____8515
                           in
                        let e1 =
                          let uu____8523 =
                            let uu____8528 =
                              let uu____8529 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____8529]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____8528
                             in
                          uu____8523 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8563 =
                          let uu____8569 =
                            let uu____8571 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____8571
                             in
                          (FStar_Errors.Warning_CoercionNotFound, uu____8569)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____8563);
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
            (((let uu____8608 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____8608) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc)
          else
            (let is_t_term t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8625 =
                 let uu____8626 = FStar_Syntax_Subst.compress t2  in
                 uu____8626.FStar_Syntax_Syntax.n  in
               match uu____8625 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____8631 -> false  in
             let is_t_term_view t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8641 =
                 let uu____8642 = FStar_Syntax_Subst.compress t2  in
                 uu____8642.FStar_Syntax_Syntax.n  in
               match uu____8641 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____8647 -> false  in
             let is_type1 t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8657 =
                 let uu____8658 = FStar_Syntax_Subst.compress t2  in
                 uu____8658.FStar_Syntax_Syntax.n  in
               match uu____8657 with
               | FStar_Syntax_Syntax.Tm_type uu____8662 -> true
               | uu____8664 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____8667 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____8667 with
             | (head1,args) ->
                 ((let uu____8715 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____8715
                   then
                     let uu____8719 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____8721 = FStar_Syntax_Print.term_to_string e  in
                     let uu____8723 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____8725 = FStar_Syntax_Print.term_to_string t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____8719 uu____8721 uu____8723 uu____8725
                   else ());
                  (let is_erased env1 t1 t2 =
                     let uu____8747 = FStar_Syntax_Util.head_and_args t2  in
                     match uu____8747 with
                     | (head2,args1) ->
                         let uu____8791 =
                           let uu____8806 =
                             let uu____8807 =
                               FStar_Syntax_Util.un_uinst head2  in
                             uu____8807.FStar_Syntax_Syntax.n  in
                           (uu____8806, args1)  in
                         (match uu____8791 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(x,FStar_Pervasives_Native.None )::[]) ->
                              (FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.erased_lid)
                                && (FStar_Syntax_Util.term_eq x t1)
                          | uu____8855 -> false)
                      in
                   let uu____8871 =
                     let uu____8886 =
                       let uu____8887 = FStar_Syntax_Util.un_uinst head1  in
                       uu____8887.FStar_Syntax_Syntax.n  in
                     (uu____8886, args)  in
                   match uu____8871 with
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
                   | uu____9012 when is_erased env t res_typ ->
                       let uu____9027 =
                         let uu____9028 =
                           env.FStar_TypeChecker_Env.universe_of env t  in
                         [uu____9028]  in
                       let uu____9029 =
                         let uu____9030 = FStar_Syntax_Syntax.iarg t  in
                         [uu____9030]  in
                       coerce_with env e lc t FStar_Parser_Const.reveal
                         uu____9027 uu____9029 FStar_Syntax_Syntax.mk_GTotal
                   | uu____9055 when is_erased env res_typ t ->
                       let uu____9070 =
                         let uu____9071 =
                           env.FStar_TypeChecker_Env.universe_of env res_typ
                            in
                         [uu____9071]  in
                       let uu____9072 =
                         let uu____9073 = FStar_Syntax_Syntax.iarg res_typ
                            in
                         [uu____9073]  in
                       coerce_with env e lc t FStar_Parser_Const.hide
                         uu____9070 uu____9072 FStar_Syntax_Syntax.mk_Total
                   | uu____9098 -> (e, lc))))
  
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
        let uu____9143 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____9143 with
        | (hd1,args) ->
            let uu____9192 =
              let uu____9207 =
                let uu____9208 = FStar_Syntax_Subst.compress hd1  in
                uu____9208.FStar_Syntax_Syntax.n  in
              (uu____9207, args)  in
            (match uu____9192 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____9246 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Total
                    in
                 FStar_All.pipe_left
                   (fun _9273  -> FStar_Pervasives_Native.Some _9273)
                   uu____9246
             | uu____9274 -> FStar_Pervasives_Native.None)
  
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
          (let uu____9327 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____9327
           then
             let uu____9330 = FStar_Syntax_Print.term_to_string e  in
             let uu____9332 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____9334 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____9330 uu____9332 uu____9334
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____9344 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____9344 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____9369 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____9395 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____9395, false)
             else
               (let uu____9405 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____9405, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____9418) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____9430 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____9430
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1126_9446 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1126_9446.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1126_9446.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1126_9446.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____9453 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____9453 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____9469 =
                      let uu____9470 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____9470 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____9490 =
                            let uu____9492 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____9492 = FStar_Syntax_Util.Equal  in
                          if uu____9490
                          then
                            ((let uu____9499 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____9499
                              then
                                let uu____9503 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____9505 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____9503 uu____9505
                              else ());
                             (let uu____9510 = set_result_typ1 c  in
                              (uu____9510, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____9517 ->
                                   true
                               | uu____9525 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____9534 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____9534
                                  in
                               let lc1 =
                                 let uu____9536 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____9537 =
                                   let uu____9538 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____9538)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____9536 uu____9537
                                  in
                               ((let uu____9542 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____9542
                                 then
                                   let uu____9546 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____9548 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____9550 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____9552 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____9546 uu____9548 uu____9550
                                     uu____9552
                                 else ());
                                (let uu____9557 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____9557 with
                                 | (c1,g_lc) ->
                                     let uu____9568 = set_result_typ1 c1  in
                                     let uu____9569 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____9568, uu____9569)))
                             else
                               ((let uu____9573 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____9573
                                 then
                                   let uu____9577 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____9579 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____9577 uu____9579
                                 else ());
                                (let uu____9584 = set_result_typ1 c  in
                                 (uu____9584, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1163_9588 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1163_9588.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1163_9588.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1163_9588.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____9598 =
                      let uu____9599 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____9599
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____9609 =
                           let uu____9610 = FStar_Syntax_Subst.compress f1
                              in
                           uu____9610.FStar_Syntax_Syntax.n  in
                         match uu____9609 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____9617,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____9619;
                                           FStar_Syntax_Syntax.vars =
                                             uu____9620;_},uu____9621)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1179_9647 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1179_9647.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1179_9647.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1179_9647.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____9648 ->
                             let uu____9649 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____9649 with
                              | (c,g_c) ->
                                  ((let uu____9661 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____9661
                                    then
                                      let uu____9665 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____9667 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____9669 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____9671 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____9665 uu____9667 uu____9669
                                        uu____9671
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
                                        let uu____9684 =
                                          let uu____9689 =
                                            let uu____9690 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____9690]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____9689
                                           in
                                        uu____9684
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____9717 =
                                      let uu____9722 =
                                        FStar_All.pipe_left
                                          (fun _9743  ->
                                             FStar_Pervasives_Native.Some
                                               _9743)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____9744 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____9745 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____9746 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____9722
                                        uu____9744 e uu____9745 uu____9746
                                       in
                                    match uu____9717 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1197_9754 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1197_9754.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1197_9754.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____9756 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____9756
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____9759 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____9759 with
                                         | (c2,g_lc) ->
                                             ((let uu____9771 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____9771
                                               then
                                                 let uu____9775 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____9775
                                               else ());
                                              (let uu____9780 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____9780))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_9789  ->
                              match uu___6_9789 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____9792 -> []))
                       in
                    let lc1 =
                      let uu____9794 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____9794 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1213_9796 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1213_9796.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1213_9796.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1213_9796.FStar_TypeChecker_Common.implicits)
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
        let uu____9832 =
          let uu____9835 =
            let uu____9840 =
              let uu____9841 =
                let uu____9850 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____9850  in
              [uu____9841]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____9840  in
          uu____9835 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____9832  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____9873 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____9873
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____9892 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____9908 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____9925 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____9925
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____9941)::(ens,uu____9943)::uu____9944 ->
                    let uu____9987 =
                      let uu____9990 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____9990  in
                    let uu____9991 =
                      let uu____9992 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____9992  in
                    (uu____9987, uu____9991)
                | uu____9995 ->
                    let uu____10006 =
                      let uu____10012 =
                        let uu____10014 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____10014
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____10012)
                       in
                    FStar_Errors.raise_error uu____10006
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____10034)::uu____10035 ->
                    let uu____10062 =
                      let uu____10067 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____10067
                       in
                    (match uu____10062 with
                     | (us_r,uu____10099) ->
                         let uu____10100 =
                           let uu____10105 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____10105
                            in
                         (match uu____10100 with
                          | (us_e,uu____10137) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____10140 =
                                  let uu____10141 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10141
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10140
                                  us_r
                                 in
                              let as_ens =
                                let uu____10143 =
                                  let uu____10144 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10144
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10143
                                  us_e
                                 in
                              let req =
                                let uu____10148 =
                                  let uu____10153 =
                                    let uu____10154 =
                                      let uu____10165 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10165]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10154
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____10153
                                   in
                                uu____10148 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____10205 =
                                  let uu____10210 =
                                    let uu____10211 =
                                      let uu____10222 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10222]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10211
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____10210
                                   in
                                uu____10205 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____10259 =
                                let uu____10262 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____10262  in
                              let uu____10263 =
                                let uu____10264 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____10264  in
                              (uu____10259, uu____10263)))
                | uu____10267 -> failwith "Impossible"))
  
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
        (let uu____10306 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____10306
         then
           let uu____10311 = FStar_Syntax_Print.term_to_string tm  in
           let uu____10313 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____10311
             uu____10313
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
          (let uu____10372 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____10372
           then
             let uu____10377 = FStar_Syntax_Print.term_to_string tm  in
             let uu____10379 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____10377
               uu____10379
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____10390 =
      let uu____10392 =
        let uu____10393 = FStar_Syntax_Subst.compress t  in
        uu____10393.FStar_Syntax_Syntax.n  in
      match uu____10392 with
      | FStar_Syntax_Syntax.Tm_app uu____10397 -> false
      | uu____10415 -> true  in
    if uu____10390
    then t
    else
      (let uu____10420 = FStar_Syntax_Util.head_and_args t  in
       match uu____10420 with
       | (head1,args) ->
           let uu____10463 =
             let uu____10465 =
               let uu____10466 = FStar_Syntax_Subst.compress head1  in
               uu____10466.FStar_Syntax_Syntax.n  in
             match uu____10465 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____10471 -> false  in
           if uu____10463
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____10503 ->
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
          ((let uu____10550 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____10550
            then
              let uu____10553 = FStar_Syntax_Print.term_to_string e  in
              let uu____10555 = FStar_Syntax_Print.term_to_string t  in
              let uu____10557 =
                let uu____10559 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____10559
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____10553 uu____10555 uu____10557
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____10572 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____10572 with
              | (formals,uu____10588) ->
                  let n_implicits =
                    let uu____10610 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____10688  ->
                              match uu____10688 with
                              | (uu____10696,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____10703 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____10703 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____10610 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____10828 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____10828 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____10842 =
                      let uu____10848 =
                        let uu____10850 = FStar_Util.string_of_int n_expected
                           in
                        let uu____10852 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____10854 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____10850 uu____10852 uu____10854
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____10848)
                       in
                    let uu____10858 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____10842 uu____10858
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_10876 =
              match uu___7_10876 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____10919 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____10919 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _11050,uu____11037)
                           when _11050 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____11083,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____11085))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____11119 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____11119 with
                            | (v1,uu____11160,g) ->
                                ((let uu____11175 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____11175
                                  then
                                    let uu____11178 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____11178
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____11188 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____11188 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____11281 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____11281))))
                       | (uu____11308,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____11345 =
                             let uu____11358 =
                               let uu____11365 =
                                 let uu____11370 = FStar_Dyn.mkdyn env  in
                                 (uu____11370, tau)  in
                               FStar_Pervasives_Native.Some uu____11365  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____11358
                              in
                           (match uu____11345 with
                            | (v1,uu____11403,g) ->
                                ((let uu____11418 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____11418
                                  then
                                    let uu____11421 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____11421
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____11431 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____11431 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____11524 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____11524))))
                       | (uu____11551,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____11599 =
                       let uu____11626 = inst_n_binders t1  in
                       aux [] uu____11626 bs1  in
                     (match uu____11599 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____11698) -> (e, torig, guard)
                           | (uu____11729,[]) when
                               let uu____11760 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____11760 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11762 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____11790 ->
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
            | uu____11803 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____11815 =
      let uu____11819 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____11819
        (FStar_List.map
           (fun u  ->
              let uu____11831 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____11831 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____11815 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____11859 = FStar_Util.set_is_empty x  in
      if uu____11859
      then []
      else
        (let s =
           let uu____11877 =
             let uu____11880 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____11880  in
           FStar_All.pipe_right uu____11877 FStar_Util.set_elements  in
         (let uu____11896 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____11896
          then
            let uu____11901 =
              let uu____11903 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____11903  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____11901
          else ());
         (let r =
            let uu____11912 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____11912  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____11951 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____11951
                     then
                       let uu____11956 =
                         let uu____11958 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____11958
                          in
                       let uu____11962 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____11964 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____11956 uu____11962 uu____11964
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
        let uu____11994 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____11994 FStar_Util.set_elements  in
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
        | ([],uu____12033) -> generalized_univ_names
        | (uu____12040,[]) -> explicit_univ_names
        | uu____12047 ->
            let uu____12056 =
              let uu____12062 =
                let uu____12064 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____12064
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____12062)
               in
            FStar_Errors.raise_error uu____12056 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____12086 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____12086
       then
         let uu____12091 = FStar_Syntax_Print.term_to_string t  in
         let uu____12093 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____12091 uu____12093
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____12102 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____12102
        then
          let uu____12107 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____12107
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____12116 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____12116
         then
           let uu____12121 = FStar_Syntax_Print.term_to_string t  in
           let uu____12123 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____12121 uu____12123
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
        let uu____12207 =
          let uu____12209 =
            FStar_Util.for_all
              (fun uu____12223  ->
                 match uu____12223 with
                 | (uu____12233,uu____12234,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____12209  in
        if uu____12207
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____12286 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____12286
              then
                let uu____12289 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____12289
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____12296 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____12296
               then
                 let uu____12299 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____12299
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____12317 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____12317 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____12351 =
             match uu____12351 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____12388 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____12388
                   then
                     let uu____12393 =
                       let uu____12395 =
                         let uu____12399 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____12399
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____12395
                         (FStar_String.concat ", ")
                        in
                     let uu____12447 =
                       let uu____12449 =
                         let uu____12453 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____12453
                           (FStar_List.map
                              (fun u  ->
                                 let uu____12466 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____12468 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____12466
                                   uu____12468))
                          in
                       FStar_All.pipe_right uu____12449
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____12393
                       uu____12447
                   else ());
                  (let univs2 =
                     let uu____12482 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____12494 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____12494) univs1
                       uu____12482
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____12501 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____12501
                    then
                      let uu____12506 =
                        let uu____12508 =
                          let uu____12512 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____12512
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____12508
                          (FStar_String.concat ", ")
                         in
                      let uu____12560 =
                        let uu____12562 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____12576 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____12578 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____12576
                                    uu____12578))
                           in
                        FStar_All.pipe_right uu____12562
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____12506 uu____12560
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____12599 =
             let uu____12616 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____12616  in
           match uu____12599 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____12706 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____12706
                 then ()
                 else
                   (let uu____12711 = lec_hd  in
                    match uu____12711 with
                    | (lb1,uu____12719,uu____12720) ->
                        let uu____12721 = lec2  in
                        (match uu____12721 with
                         | (lb2,uu____12729,uu____12730) ->
                             let msg =
                               let uu____12733 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____12735 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____12733 uu____12735
                                in
                             let uu____12738 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____12738))
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
                 let uu____12806 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____12806
                 then ()
                 else
                   (let uu____12811 = lec_hd  in
                    match uu____12811 with
                    | (lb1,uu____12819,uu____12820) ->
                        let uu____12821 = lec2  in
                        (match uu____12821 with
                         | (lb2,uu____12829,uu____12830) ->
                             let msg =
                               let uu____12833 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____12835 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____12833 uu____12835
                                in
                             let uu____12838 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____12838))
                  in
               let lecs1 =
                 let uu____12849 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____12902 = univs_and_uvars_of_lec this_lec  in
                        match uu____12902 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____12849 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____13007 = lec_hd  in
                   match uu____13007 with
                   | (lbname,e,c) ->
                       let uu____13017 =
                         let uu____13023 =
                           let uu____13025 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____13027 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____13029 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____13025 uu____13027 uu____13029
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____13023)
                          in
                       let uu____13033 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____13017 uu____13033
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____13052 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____13052 with
                         | FStar_Pervasives_Native.Some uu____13061 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____13069 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____13073 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____13073 with
                              | (bs,kres) ->
                                  ((let uu____13117 =
                                      let uu____13118 =
                                        let uu____13121 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____13121
                                         in
                                      uu____13118.FStar_Syntax_Syntax.n  in
                                    match uu____13117 with
                                    | FStar_Syntax_Syntax.Tm_type uu____13122
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____13126 =
                                          let uu____13128 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____13128  in
                                        if uu____13126
                                        then fail1 kres
                                        else ()
                                    | uu____13133 -> fail1 kres);
                                   (let a =
                                      let uu____13135 =
                                        let uu____13138 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _13141  ->
                                             FStar_Pervasives_Native.Some
                                               _13141) uu____13138
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____13135
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____13149 ->
                                          let uu____13158 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____13158
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
                      (fun uu____13261  ->
                         match uu____13261 with
                         | (lbname,e,c) ->
                             let uu____13307 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____13368 ->
                                   let uu____13381 = (e, c)  in
                                   (match uu____13381 with
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
                                                (fun uu____13421  ->
                                                   match uu____13421 with
                                                   | (x,uu____13427) ->
                                                       let uu____13428 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____13428)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____13446 =
                                                let uu____13448 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____13448
                                                 in
                                              if uu____13446
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
                                          let uu____13457 =
                                            let uu____13458 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____13458.FStar_Syntax_Syntax.n
                                             in
                                          match uu____13457 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____13483 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____13483 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____13494 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____13498 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____13498, gen_tvars))
                                in
                             (match uu____13307 with
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
        (let uu____13645 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____13645
         then
           let uu____13648 =
             let uu____13650 =
               FStar_List.map
                 (fun uu____13665  ->
                    match uu____13665 with
                    | (lb,uu____13674,uu____13675) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____13650 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____13648
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____13701  ->
                match uu____13701 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____13730 = gen env is_rec lecs  in
           match uu____13730 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____13829  ->
                       match uu____13829 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____13891 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____13891
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____13939  ->
                           match uu____13939 with
                           | (l,us,e,c,gvs) ->
                               let uu____13973 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____13975 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____13977 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____13979 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____13981 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____13973 uu____13975 uu____13977
                                 uu____13979 uu____13981))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____14026  ->
                match uu____14026 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____14070 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____14070, t, c, gvs)) univnames_lecs
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
              (let uu____14135 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____14135 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____14141 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _14144  -> FStar_Pervasives_Native.Some _14144)
                     uu____14141)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1666_14164 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1666_14164.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1666_14164.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____14165 -> e2  in
          let uu____14166 = maybe_coerce_lc env1 e lc t2  in
          match uu____14166 with
          | (e1,lc1) ->
              let uu____14179 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____14179 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14188 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____14194 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____14188 uu____14194
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____14203 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____14203
                     then
                       let uu____14208 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____14208
                     else ());
                    (let uu____14214 = decorate e1 t2  in
                     (uu____14214, lc1, g))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____14242 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____14242
         then
           let uu____14245 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____14245
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____14259 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____14259 with
         | (c,g_c) ->
             let uu____14271 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____14271
             then
               let uu____14279 =
                 let uu____14281 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____14281  in
               (uu____14279, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____14289 =
                    let uu____14290 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____14290
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____14289
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____14291 = check_trivial_precondition env c1  in
                match uu____14291 with
                | (ct,vc,g_pre) ->
                    ((let uu____14307 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____14307
                      then
                        let uu____14312 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____14312
                      else ());
                     (let uu____14317 =
                        let uu____14319 =
                          let uu____14320 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____14320  in
                        discharge uu____14319  in
                      let uu____14321 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____14317, uu____14321)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_14355 =
        match uu___8_14355 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____14365)::[] -> f fst1
        | uu____14390 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____14402 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____14402
          (fun _14403  -> FStar_TypeChecker_Common.NonTrivial _14403)
         in
      let op_or_e e =
        let uu____14414 =
          let uu____14415 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____14415  in
        FStar_All.pipe_right uu____14414
          (fun _14418  -> FStar_TypeChecker_Common.NonTrivial _14418)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _14425  -> FStar_TypeChecker_Common.NonTrivial _14425)
         in
      let op_or_t t =
        let uu____14436 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____14436
          (fun _14439  -> FStar_TypeChecker_Common.NonTrivial _14439)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _14446  -> FStar_TypeChecker_Common.NonTrivial _14446)
         in
      let short_op_ite uu___9_14452 =
        match uu___9_14452 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____14462)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____14489)::[] ->
            let uu____14530 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____14530
              (fun _14531  -> FStar_TypeChecker_Common.NonTrivial _14531)
        | uu____14532 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____14544 =
          let uu____14552 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____14552)  in
        let uu____14560 =
          let uu____14570 =
            let uu____14578 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____14578)  in
          let uu____14586 =
            let uu____14596 =
              let uu____14604 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____14604)  in
            let uu____14612 =
              let uu____14622 =
                let uu____14630 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____14630)  in
              let uu____14638 =
                let uu____14648 =
                  let uu____14656 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____14656)  in
                [uu____14648; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____14622 :: uu____14638  in
            uu____14596 :: uu____14612  in
          uu____14570 :: uu____14586  in
        uu____14544 :: uu____14560  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____14718 =
            FStar_Util.find_map table
              (fun uu____14733  ->
                 match uu____14733 with
                 | (x,mk1) ->
                     let uu____14750 = FStar_Ident.lid_equals x lid  in
                     if uu____14750
                     then
                       let uu____14755 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____14755
                     else FStar_Pervasives_Native.None)
             in
          (match uu____14718 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____14759 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____14767 =
      let uu____14768 = FStar_Syntax_Util.un_uinst l  in
      uu____14768.FStar_Syntax_Syntax.n  in
    match uu____14767 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____14773 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____14809)::uu____14810 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____14829 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____14838,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____14839))::uu____14840 -> bs
      | uu____14858 ->
          let uu____14859 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____14859 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____14863 =
                 let uu____14864 = FStar_Syntax_Subst.compress t  in
                 uu____14864.FStar_Syntax_Syntax.n  in
               (match uu____14863 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____14868) ->
                    let uu____14889 =
                      FStar_Util.prefix_until
                        (fun uu___10_14929  ->
                           match uu___10_14929 with
                           | (uu____14937,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____14938)) ->
                               false
                           | uu____14943 -> true) bs'
                       in
                    (match uu____14889 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____14979,uu____14980) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____15052,uu____15053) ->
                         let uu____15126 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____15146  ->
                                   match uu____15146 with
                                   | (x,uu____15155) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____15126
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____15204  ->
                                     match uu____15204 with
                                     | (x,i) ->
                                         let uu____15223 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____15223, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____15234 -> bs))
  
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
            let uu____15263 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____15263
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
          let uu____15294 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____15294
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
        (let uu____15337 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____15337
         then
           ((let uu____15342 = FStar_Ident.text_of_lid lident  in
             d uu____15342);
            (let uu____15344 = FStar_Ident.text_of_lid lident  in
             let uu____15346 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____15344 uu____15346))
         else ());
        (let fv =
           let uu____15352 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____15352
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
         let uu____15364 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1826_15366 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1826_15366.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1826_15366.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1826_15366.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1826_15366.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___1826_15366.FStar_Syntax_Syntax.sigopts)
           }), uu____15364))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_15384 =
        match uu___11_15384 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____15387 -> false  in
      let reducibility uu___12_15395 =
        match uu___12_15395 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____15402 -> false  in
      let assumption uu___13_15410 =
        match uu___13_15410 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____15414 -> false  in
      let reification uu___14_15422 =
        match uu___14_15422 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____15425 -> true
        | uu____15427 -> false  in
      let inferred uu___15_15435 =
        match uu___15_15435 with
        | FStar_Syntax_Syntax.Discriminator uu____15437 -> true
        | FStar_Syntax_Syntax.Projector uu____15439 -> true
        | FStar_Syntax_Syntax.RecordType uu____15445 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____15455 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____15468 -> false  in
      let has_eq uu___16_15476 =
        match uu___16_15476 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____15480 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____15559 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____15566 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____15599 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____15599))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____15630 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____15630
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
           | FStar_Syntax_Syntax.Sig_bundle uu____15650 ->
               let uu____15659 =
                 let uu____15661 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_15667  ->
                           match uu___17_15667 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____15670 -> false))
                    in
                 Prims.op_Negation uu____15661  in
               if uu____15659
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____15677 -> ()
           | uu____15684 ->
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
      let uu____15698 =
        let uu____15700 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_15706  ->
                  match uu___18_15706 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____15709 -> false))
           in
        FStar_All.pipe_right uu____15700 Prims.op_Negation  in
      if uu____15698
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____15730 =
            let uu____15736 =
              let uu____15738 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____15738 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____15736)  in
          FStar_Errors.raise_error uu____15730 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____15756 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____15764 =
            let uu____15766 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____15766  in
          if uu____15764 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____15777),uu____15778) ->
              ((let uu____15790 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____15790
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____15799 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____15799
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____15810 ->
              ((let uu____15820 =
                  let uu____15822 =
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
                  Prims.op_Negation uu____15822  in
                if uu____15820 then err'1 () else ());
               (let uu____15832 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_15838  ->
                           match uu___19_15838 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____15841 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____15832
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____15847 ->
              let uu____15854 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____15854 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____15862 ->
              let uu____15869 =
                let uu____15871 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____15871  in
              if uu____15869 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____15881 ->
              let uu____15882 =
                let uu____15884 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____15884  in
              if uu____15882 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15894 ->
              let uu____15895 =
                let uu____15897 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____15897  in
              if uu____15895 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15907 ->
              let uu____15920 =
                let uu____15922 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____15922  in
              if uu____15920 then err'1 () else ()
          | uu____15932 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____15971 =
          let uu____15972 = FStar_Syntax_Subst.compress t1  in
          uu____15972.FStar_Syntax_Syntax.n  in
        match uu____15971 with
        | FStar_Syntax_Syntax.Tm_arrow uu____15976 ->
            let uu____15991 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____15991 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____16024;
               FStar_Syntax_Syntax.index = uu____16025;
               FStar_Syntax_Syntax.sort = t2;_},uu____16027)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____16036) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____16062) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____16068 -> false
      
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
        (let uu____16078 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____16078
         then
           let uu____16083 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____16083
         else ());
        res
       in aux g t
  
let (fresh_effect_repr :
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
                  let uu____16144 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____16144 r  in
                let uu____16154 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____16154 with
                | (uu____16163,signature) ->
                    let uu____16165 =
                      let uu____16166 = FStar_Syntax_Subst.compress signature
                         in
                      uu____16166.FStar_Syntax_Syntax.n  in
                    (match uu____16165 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16174) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____16222 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____16237 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____16239 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____16237 eff_name.FStar_Ident.str
                                       uu____16239) r
                                 in
                              (match uu____16222 with
                               | (is,g) ->
                                   let uu____16252 =
                                     match repr_ts with
                                     | (uu____16253,{
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_unknown
                                                        ;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____16254;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____16255;_})
                                         ->
                                         let eff_c =
                                           let uu____16265 =
                                             let uu____16266 =
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
                                                 = uu____16266;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____16265
                                            in
                                         let uu____16285 =
                                           let uu____16292 =
                                             let uu____16293 =
                                               let uu____16308 =
                                                 let uu____16317 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____16317]  in
                                               (uu____16308, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____16293
                                              in
                                           FStar_Syntax_Syntax.mk uu____16292
                                            in
                                         uu____16285
                                           FStar_Pervasives_Native.None r
                                     | uu____16346 ->
                                         let repr =
                                           let uu____16348 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____16348
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____16357 =
                                           let uu____16362 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____16362
                                            in
                                         uu____16357
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____16252, g))
                          | uu____16371 -> fail1 signature)
                     | uu____16372 -> fail1 signature)
  
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
            let uu____16403 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____16403
              (fun ed  ->
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature
                   ed.FStar_Syntax_Syntax.repr u a_tm)
  
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
              let uu____16441 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____16441 with
              | (uu____16446,sig_tm) ->
                  let fail1 t =
                    let uu____16454 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____16454 r  in
                  let uu____16460 =
                    let uu____16461 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____16461.FStar_Syntax_Syntax.n  in
                  (match uu____16460 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16465) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____16488)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____16510 -> fail1 sig_tm)
                   | uu____16511 -> fail1 sig_tm)
  
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
          (let uu____16542 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____16542
           then
             let uu____16547 = FStar_Syntax_Print.comp_to_string c  in
             let uu____16549 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____16547 uu____16549
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____16579 =
               let uu____16580 =
                 let uu____16586 =
                   let uu____16588 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____16590 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____16588 uu____16590
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____16586)  in
               FStar_Errors.raise_error uu____16580 r  in
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered
             then
               match repr1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_app (uu____16602,uu____16603::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____16671 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____16676,c1) ->
                    let uu____16698 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____16698
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
                | uu____16733 -> err ())
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____16735 =
             let uu____16746 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____16747 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____16746, (ct.FStar_Syntax_Syntax.result_typ), uu____16747)
              in
           match uu____16735 with
           | (u,a,c_is) ->
               let uu____16795 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____16795 with
                | (uu____16804,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____16815 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____16817 = FStar_Ident.string_of_lid tgt  in
                      let uu____16819 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____16815 uu____16817 s uu____16819
                       in
                    let uu____16822 =
                      let uu____16855 =
                        let uu____16856 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____16856.FStar_Syntax_Syntax.n  in
                      match uu____16855 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____16920 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____16920 with
                           | (a_b::bs1,c2) ->
                               let uu____16980 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____17042 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16980, uu____17042))
                      | uu____17069 ->
                          let uu____17070 =
                            let uu____17076 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____17076)
                             in
                          FStar_Errors.raise_error uu____17070 r
                       in
                    (match uu____16822 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____17194 =
                           let uu____17201 =
                             let uu____17202 =
                               let uu____17203 =
                                 let uu____17210 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____17210, a)  in
                               FStar_Syntax_Syntax.NT uu____17203  in
                             [uu____17202]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____17201
                             (fun b  ->
                                let uu____17227 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____17229 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____17231 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____17233 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____17227 uu____17229 uu____17231
                                  uu____17233) r
                            in
                         (match uu____17194 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____17247 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____17247
                                then
                                  let uu____17252 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____17261 =
                                             let uu____17263 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____17263
                                              in
                                           Prims.op_Hat s uu____17261) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____17252
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____17294 =
                                           let uu____17301 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____17301, t)  in
                                         FStar_Syntax_Syntax.NT uu____17294)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____17320 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____17320
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____17326 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____17326
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____17335 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____17335)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____17339 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____17339
                                   in
                                let c1 =
                                  let uu____17342 =
                                    let uu____17343 =
                                      let uu____17354 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____17354
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____17343;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____17342  in
                                (let uu____17374 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____17374
                                 then
                                   let uu____17379 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____17379
                                 else ());
                                (let uu____17384 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____17384))))))))
  
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
              let uu____17414 =
                let uu____17419 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____17419
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____17414 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____17462 =
                let uu____17463 =
                  let uu____17466 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____17466
                    FStar_Syntax_Subst.compress
                   in
                uu____17463.FStar_Syntax_Syntax.n  in
              match uu____17462 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____17489::bs,uu____17491)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____17531 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____17531
                    FStar_Pervasives_Native.fst
              | uu____17637 ->
                  let uu____17638 =
                    let uu____17644 =
                      let uu____17646 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____17646
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____17644)  in
                  FStar_Errors.raise_error uu____17638
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let e_reified =
              let uu____17663 =
                let uu____17666 =
                  let uu____17667 =
                    let uu____17676 =
                      FStar_All.pipe_right sub1.FStar_Syntax_Syntax.source
                        (FStar_TypeChecker_Env.get_effect_decl env)
                       in
                    FStar_All.pipe_right uu____17676
                      (fun ed  -> ed.FStar_Syntax_Syntax.repr)
                     in
                  FStar_All.pipe_right uu____17667
                    FStar_Pervasives_Native.snd
                   in
                FStar_All.pipe_right uu____17666 FStar_Syntax_Subst.compress
                 in
              match uu____17663 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____17693;
                  FStar_Syntax_Syntax.vars = uu____17694;_} ->
                  let uu____17697 =
                    let uu____17698 =
                      FStar_Syntax_Syntax.null_binder
                        FStar_Syntax_Syntax.t_unit
                       in
                    [uu____17698]  in
                  FStar_Syntax_Util.abs uu____17697 e
                    FStar_Pervasives_Native.None
              | uu____17717 ->
                  reify_body env [FStar_TypeChecker_Env.Inlining] e
               in
            let args =
              let uu____17731 = FStar_Syntax_Syntax.as_arg a  in
              let uu____17740 =
                let uu____17751 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____17787  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____17794 =
                  let uu____17805 = FStar_Syntax_Syntax.as_arg e_reified  in
                  [uu____17805]  in
                FStar_List.append uu____17751 uu____17794  in
              uu____17731 :: uu____17740  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____17869 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____17869
      then
        let uu____17872 =
          let uu____17885 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____17885
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____17872;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____17920 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____17920 with
           | (uu____17929,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____17948 =
                 let uu____17949 =
                   let uu___2203_17950 = ct  in
                   let uu____17951 =
                     let uu____17962 =
                       let uu____17971 =
                         let uu____17972 =
                           let uu____17979 =
                             let uu____17980 =
                               let uu____17997 =
                                 let uu____18008 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____18008; wp]  in
                               (lift_t, uu____17997)  in
                             FStar_Syntax_Syntax.Tm_app uu____17980  in
                           FStar_Syntax_Syntax.mk uu____17979  in
                         uu____17972 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____17971
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____17962]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2203_17950.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2203_17950.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____17951;
                     FStar_Syntax_Syntax.flags =
                       (uu___2203_17950.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____17949  in
               (uu____17948, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____18108 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____18108 with
           | (uu____18115,lift_t) ->
               let uu____18117 =
                 let uu____18124 =
                   let uu____18125 =
                     let uu____18142 =
                       let uu____18153 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____18162 =
                         let uu____18173 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____18182 =
                           let uu____18193 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____18193]  in
                         uu____18173 :: uu____18182  in
                       uu____18153 :: uu____18162  in
                     (lift_t, uu____18142)  in
                   FStar_Syntax_Syntax.Tm_app uu____18125  in
                 FStar_Syntax_Syntax.mk uu____18124  in
               uu____18117 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____18246 =
           let uu____18259 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____18259 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____18246;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____18295  ->
                        fun uu____18296  -> fun e  -> FStar_Util.return_all e))
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
        let uu____18326 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____18326 with
        | (uu____18331,t) ->
            let err n1 =
              let uu____18341 =
                let uu____18347 =
                  let uu____18349 = FStar_Ident.string_of_lid datacon  in
                  let uu____18351 = FStar_Util.string_of_int n1  in
                  let uu____18353 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____18349 uu____18351 uu____18353
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____18347)
                 in
              let uu____18357 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____18341 uu____18357  in
            let uu____18358 =
              let uu____18359 = FStar_Syntax_Subst.compress t  in
              uu____18359.FStar_Syntax_Syntax.n  in
            (match uu____18358 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18363) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____18418  ->
                           match uu____18418 with
                           | (uu____18426,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____18435 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____18467 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____18467
                      FStar_Pervasives_Native.fst)
             | uu____18478 -> err Prims.int_zero)
  