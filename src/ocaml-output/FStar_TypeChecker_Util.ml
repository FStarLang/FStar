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
          let uu____1110 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1111 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join_opt env uu____1110 uu____1111  in
        match uu____1101 with
        | FStar_Pervasives_Native.Some (m,uu____1113,uu____1114) -> m
        | FStar_Pervasives_Native.None  ->
            let uu____1127 =
              FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2  in
            (match uu____1127 with
             | FStar_Pervasives_Native.Some (m,uu____1141) -> m
             | FStar_Pervasives_Native.None  ->
                 let uu____1174 =
                   let uu____1180 =
                     let uu____1182 = FStar_Syntax_Print.lid_to_string l1  in
                     let uu____1184 = FStar_Syntax_Print.lid_to_string l2  in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____1182
                       uu____1184
                      in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____1180)
                    in
                 FStar_Errors.raise_error uu____1174
                   env.FStar_TypeChecker_Env.range)
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1204 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1204
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
            let uu____1259 =
              FStar_TypeChecker_Env.join env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____1259 with
            | (m,lift1,lift2) ->
                let uu____1277 = lift_comp env c11 lift1  in
                (match uu____1277 with
                 | (c12,g1) ->
                     let uu____1292 =
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
                          let uu____1331 = lift_comp env_x c21 lift2  in
                          match uu____1331 with
                          | (c22,g2) ->
                              let uu____1342 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____1342))
                        in
                     (match uu____1292 with
                      | (c22,g2) ->
                          let uu____1365 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (m, c12, c22, uu____1365)))
  
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
            let uu____1426 =
              let uu____1427 =
                let uu____1438 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1438]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1427;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1426
  
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
          let uu____1522 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1522
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1534 =
      let uu____1535 = FStar_Syntax_Subst.compress t  in
      uu____1535.FStar_Syntax_Syntax.n  in
    match uu____1534 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1539 -> true
    | uu____1555 -> false
  
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
              let uu____1625 =
                let uu____1627 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1627  in
              if uu____1625
              then f
              else (let uu____1634 = reason1 ()  in label uu____1634 r f)
  
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
            let uu___253_1655 = g  in
            let uu____1656 =
              let uu____1657 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1657  in
            {
              FStar_TypeChecker_Common.guard_f = uu____1656;
              FStar_TypeChecker_Common.deferred =
                (uu___253_1655.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___253_1655.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___253_1655.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1678 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1678
        then c
        else
          (let uu____1683 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1683
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____1725 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____1725 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____1753 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____1753]  in
                       let us =
                         let uu____1775 =
                           let uu____1778 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____1778]  in
                         u_res :: uu____1775  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____1784 =
                         let uu____1789 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____1790 =
                           let uu____1791 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____1800 =
                             let uu____1811 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____1820 =
                               let uu____1831 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____1831]  in
                             uu____1811 :: uu____1820  in
                           uu____1791 :: uu____1800  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1789 uu____1790
                          in
                       uu____1784 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1873 = destruct_wp_comp c1  in
              match uu____1873 with
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
                let uu____1913 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____1913
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
                  let uu____1963 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____1963
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_1976  ->
            match uu___0_1976 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1979 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____2004 =
            let uu____2007 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2007 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____2004
            (fun c  ->
               (let uu____2063 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2063) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2067 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2067)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2078 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2078 with
                | (head1,uu____2095) ->
                    let uu____2116 =
                      let uu____2117 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2117.FStar_Syntax_Syntax.n  in
                    (match uu____2116 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2122 =
                           let uu____2124 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2124
                            in
                         Prims.op_Negation uu____2122
                     | uu____2125 -> true)))
              &&
              (let uu____2128 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2128)
  
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
            let uu____2156 =
              let uu____2158 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2158  in
            if uu____2156
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2165 = FStar_Syntax_Util.is_unit t  in
               if uu____2165
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
                    let uu____2174 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2174
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2179 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2179 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let ret_wp =
                             FStar_All.pipe_right m
                               FStar_Syntax_Util.get_return_vc_combinator
                              in
                           let uu____2190 =
                             let uu____2191 =
                               let uu____2196 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m ret_wp
                                  in
                               let uu____2197 =
                                 let uu____2198 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2207 =
                                   let uu____2218 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2218]  in
                                 uu____2198 :: uu____2207  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2196
                                 uu____2197
                                in
                             uu____2191 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2190)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2252 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2252
           then
             let uu____2257 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2259 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2261 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2257 uu____2259 uu____2261
           else ());
          c
  
let (effect_args_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool -> FStar_Range.range -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr  ->
    fun is_layered1  ->
      fun r  ->
        let err uu____2295 =
          let uu____2296 =
            let uu____2302 =
              let uu____2304 = FStar_Syntax_Print.term_to_string repr  in
              let uu____2306 = FStar_Util.string_of_bool is_layered1  in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____2304 uu____2306
               in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____2302)  in
          FStar_Errors.raise_error uu____2296 r  in
        let repr1 = FStar_Syntax_Subst.compress repr  in
        if is_layered1
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu____2318,uu____2319::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu____2387 -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu____2392,c) ->
               let uu____2414 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ
                  in
               FStar_All.pipe_right uu____2414
                 (fun ct  ->
                    FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                      (FStar_List.map FStar_Pervasives_Native.fst))
           | uu____2449 -> err ())
  
let (mk_indexed_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Syntax_Syntax.comp_typ ->
                  FStar_Syntax_Syntax.cflag Prims.list ->
                    FStar_Range.range ->
                      (FStar_Syntax_Syntax.comp *
                        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun bind_t  ->
            fun ct1  ->
              fun b  ->
                fun ct2  ->
                  fun flags  ->
                    fun r1  ->
                      (let uu____2518 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____2518
                       then
                         let uu____2523 =
                           let uu____2525 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____2525  in
                         let uu____2526 =
                           let uu____2528 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____2528  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____2523 uu____2526
                       else ());
                      (let uu____2532 =
                         let uu____2539 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____2540 =
                           FStar_TypeChecker_Env.get_effect_decl env n1  in
                         let uu____2541 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____2539, uu____2540, uu____2541)  in
                       match uu____2532 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____2549 =
                             let uu____2560 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____2561 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____2560,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____2561)
                              in
                           (match uu____2549 with
                            | (u1,t1,is1) ->
                                let uu____2595 =
                                  let uu____2606 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____2607 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____2606,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____2607)
                                   in
                                (match uu____2595 with
                                 | (u2,t2,is2) ->
                                     let uu____2641 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____2641 with
                                      | (uu____2650,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____2665 =
                                              let uu____2667 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____2667 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____2665)
                                             in
                                          let uu____2671 =
                                            let uu____2716 =
                                              let uu____2717 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____2717.FStar_Syntax_Syntax.n
                                               in
                                            match uu____2716 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____2793 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____2793 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____2878 =
                                                       let uu____2905 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2905
                                                         (fun uu____2990  ->
                                                            match uu____2990
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____3071
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____3084
                                                                  =
                                                                  let uu____3091
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____3091
                                                                   in
                                                                (l1,
                                                                  uu____3071,
                                                                  uu____3084))
                                                        in
                                                     (match uu____2878 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          let uu____3219 =
                                                            FStar_Syntax_Util.comp_to_comp_typ
                                                              c1
                                                             in
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b,
                                                            uu____3219)))
                                            | uu____3252 ->
                                                let uu____3253 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____3253 r1
                                             in
                                          (match uu____2671 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_ct)
                                               ->
                                               let uu____3378 =
                                                 let uu____3385 =
                                                   let uu____3386 =
                                                     let uu____3387 =
                                                       let uu____3394 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____3394, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____3387
                                                      in
                                                   let uu____3405 =
                                                     let uu____3408 =
                                                       let uu____3409 =
                                                         let uu____3416 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____3416, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____3409
                                                        in
                                                     [uu____3408]  in
                                                   uu____3386 :: uu____3405
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____3385
                                                   (fun b1  ->
                                                      let uu____3431 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____3433 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s:bind at %s"
                                                        uu____3431 ""
                                                        uu____3433) r1
                                                  in
                                               (match uu____3378 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____3471 =
                                                               let uu____3478
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____3478,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____3471)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____3505 =
                                                          let uu____3508 =
                                                            let uu____3509 =
                                                              let uu____3510
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____3510.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____3509
                                                             in
                                                          let uu____3519 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____3508
                                                            uu____3519 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3505
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst1))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____3532
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____3532)
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
                                                        | FStar_Pervasives_Native.Some
                                                            x ->
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                         in
                                                      let g_sort_is =
                                                        let uu____3551 =
                                                          let uu____3552 =
                                                            let uu____3555 =
                                                              let uu____3556
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____3556.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____3555
                                                             in
                                                          uu____3552.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____3551 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____3589 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____3589
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____3599
                                                                    =
                                                                    let uu____3606
                                                                    =
                                                                    let uu____3607
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____3607
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____3628
                                                                    =
                                                                    let uu____3631
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3631
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____3606,
                                                                    uu____3628)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____3599
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____3645
                                                                   =
                                                                   let uu____3648
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____3649
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____3648
                                                                    uu____3649
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____3645
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)))
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____3668 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____3676
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____3676)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3668
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let is =
                                                      let uu____3692 =
                                                        let uu____3695 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        let uu____3696 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed
                                                           in
                                                        effect_args_from_repr
                                                          uu____3695
                                                          uu____3696 r1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3692
                                                        (FStar_List.map
                                                           (FStar_Syntax_Subst.subst
                                                              subst1))
                                                       in
                                                    let c =
                                                      let uu____3703 =
                                                        let uu____3704 =
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
                                                            (p_ed.FStar_Syntax_Syntax.mname);
                                                          FStar_Syntax_Syntax.result_typ
                                                            = t2;
                                                          FStar_Syntax_Syntax.effect_args
                                                            = uu____3704;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____3703
                                                       in
                                                    ((let uu____3724 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____3724
                                                      then
                                                        let uu____3729 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____3729
                                                      else ());
                                                     (let uu____3734 =
                                                        FStar_TypeChecker_Env.conj_guards
                                                          [g_uvars;
                                                          f_guard;
                                                          g_guard]
                                                         in
                                                      (c, uu____3734)))))))))
  
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
                let uu____3779 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____3805 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____3805 with
                  | (a,kwp) ->
                      let uu____3836 = destruct_wp_comp ct1  in
                      let uu____3843 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____3836, uu____3843)
                   in
                match uu____3779 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____3896 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____3896]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____3916 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3916]
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
                      let uu____3963 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____3972 =
                        let uu____3983 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____3992 =
                          let uu____4003 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____4012 =
                            let uu____4023 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____4032 =
                              let uu____4043 =
                                let uu____4052 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____4052  in
                              [uu____4043]  in
                            uu____4023 :: uu____4032  in
                          uu____4003 :: uu____4012  in
                        uu____3983 :: uu____3992  in
                      uu____3963 :: uu____3972  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____4105 =
                        let uu____4110 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4110 wp_args  in
                      uu____4105 FStar_Pervasives_Native.None
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
              let uu____4158 = lift_comps env c1 c2 b true  in
              match uu____4158 with
              | (m,c11,c21,g_lift) ->
                  let uu____4176 =
                    let uu____4181 = FStar_Syntax_Util.comp_to_comp_typ c11
                       in
                    let uu____4182 = FStar_Syntax_Util.comp_to_comp_typ c21
                       in
                    (uu____4181, uu____4182)  in
                  (match uu____4176 with
                   | (ct1,ct2) ->
                       let uu____4189 =
                         let uu____4194 =
                           FStar_TypeChecker_Env.is_layered_effect env m  in
                         if uu____4194
                         then
                           let bind_t =
                             let uu____4202 =
                               FStar_All.pipe_right m
                                 (FStar_TypeChecker_Env.get_effect_decl env)
                                in
                             FStar_All.pipe_right uu____4202
                               FStar_Syntax_Util.get_bind_vc_combinator
                              in
                           mk_indexed_bind env m m m bind_t ct1 b ct2 flags
                             r1
                         else
                           (let uu____4205 =
                              mk_non_layered_bind env m ct1 b ct2 flags r1
                               in
                            (uu____4205, FStar_TypeChecker_Env.trivial_guard))
                          in
                       (match uu____4189 with
                        | (c,g_bind) ->
                            let uu____4212 =
                              FStar_TypeChecker_Env.conj_guard g_lift g_bind
                               in
                            (c, uu____4212)))
  
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
            let uu____4248 =
              let uu____4249 =
                let uu____4260 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____4260]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4249;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4248  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____4305 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4311  ->
              match uu___1_4311 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4314 -> false))
       in
    if uu____4305
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4326  ->
              match uu___2_4326 with
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
        let uu____4354 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4354
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____4365 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____4365  in
           let pure_assume_wp1 =
             let uu____4370 = FStar_TypeChecker_Env.get_range env  in
             let uu____4371 =
               let uu____4376 =
                 let uu____4377 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____4377]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4376  in
             uu____4371 FStar_Pervasives_Native.None uu____4370  in
           let uu____4410 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____4410)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4438 =
          let uu____4439 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____4439 with
          | (c,g_c) ->
              let uu____4450 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4450
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____4464 = weaken_comp env c f1  in
                     (match uu____4464 with
                      | (c1,g_w) ->
                          let uu____4475 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____4475)))
           in
        let uu____4476 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____4476 weaken
  
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
                 let uu____4533 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____4533  in
               let pure_assert_wp1 =
                 let uu____4538 =
                   let uu____4543 =
                     let uu____4544 =
                       let uu____4553 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____4553
                        in
                     [uu____4544]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____4543
                    in
                 uu____4538 FStar_Pervasives_Native.None r  in
               bind_pure_wp_with env pure_assert_wp1 c flags)
  
let (record_simplify :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  let x = FStar_Util.mk_ref Prims.int_zero  in
  fun env  ->
    fun guard  ->
      let n1 = FStar_ST.op_Bang x  in
      FStar_ST.op_Colon_Equals x (n1 + Prims.int_one);
      (let start = FStar_Util.now ()  in
       let g = FStar_TypeChecker_Rel.simplify_guard env guard  in
       let fin = FStar_Util.now ()  in
       (let uu____4645 = FStar_Options.debug_any ()  in
        if uu____4645
        then
          let uu____4648 = FStar_Util.string_of_int n1  in
          let uu____4650 =
            let uu____4652 =
              let uu____4654 = FStar_Util.time_diff start fin  in
              FStar_Pervasives_Native.snd uu____4654  in
            FStar_Util.string_of_int uu____4652  in
          FStar_Util.print2 "Simplify_guard %s in %s ms\n" uu____4648
            uu____4650
        else ());
       g)
  
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
            let uu____4709 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____4709
            then (lc, g0)
            else
              (let flags =
                 let uu____4721 =
                   let uu____4729 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____4729
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4721 with
                 | (maybe_trivial_post,flags) ->
                     let uu____4759 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_4767  ->
                               match uu___3_4767 with
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
                               | uu____4770 -> []))
                        in
                     FStar_List.append flags uu____4759
                  in
               let strengthen uu____4780 =
                 let uu____4781 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____4781 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____4800 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____4800 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____4807 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4807
                              then
                                let uu____4811 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____4813 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____4811 uu____4813
                              else ());
                             (let uu____4818 =
                                strengthen_comp env reason c f flags  in
                              match uu____4818 with
                              | (c1,g_s) ->
                                  let uu____4829 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____4829))))
                  in
               let uu____4830 =
                 let uu____4831 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____4831
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____4830,
                 (let uu___584_4833 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___584_4833.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___584_4833.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___584_4833.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_4842  ->
            match uu___4_4842 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4846 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____4875 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4875
          then e
          else
            (let uu____4882 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4885 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4885)
                in
             if uu____4882
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
                | uu____4955 -> false  in
              if is_unit1
              then
                let uu____4962 =
                  let uu____4964 =
                    let uu____4965 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____4965
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____4964
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____4962
                 then
                   let uu____4974 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____4974 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____5018 =
                           let uu____5021 =
                             let uu____5022 =
                               let uu____5029 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____5029, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____5022  in
                           [uu____5021]  in
                         FStar_Syntax_Subst.subst uu____5018 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____5042 = close_wp_comp env [x] c  in
                    (uu____5042, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____5045 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____5073  ->
            match uu____5073 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5093 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5093 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5106 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5106
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____5116 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____5116
                       then
                         let uu____5121 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____5121
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5128 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____5128
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5137 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____5137
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5144 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5144
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____5160 =
                  let uu____5161 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5161
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____5169 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____5169, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____5172 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____5172 with
                     | (c1,g_c1) ->
                         let uu____5183 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____5183 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____5203  ->
                                    let uu____5204 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____5206 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____5211 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____5204 uu____5206 uu____5211);
                               (let aux uu____5229 =
                                  let uu____5230 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____5230
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5261
                                        ->
                                        let uu____5262 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5262
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5294 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5294
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____5341 =
                                  let aux_with_trivial_guard uu____5371 =
                                    let uu____5372 = aux ()  in
                                    match uu____5372 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c,
                                            FStar_TypeChecker_Env.trivial_guard,
                                            reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____5430 =
                                    let uu____5432 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____5432  in
                                  if uu____5430
                                  then
                                    let uu____5448 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____5448
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           FStar_TypeChecker_Env.trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5475 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5475))
                                  else
                                    (let uu____5492 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____5492
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___683_5538 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___683_5538.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___683_5538.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____5539 =
                                           maybe_capture_unit_refinement env
                                             x1.FStar_Syntax_Syntax.sort x1 c
                                            in
                                         match uu____5539 with
                                         | (c3,g_c) ->
                                             FStar_Util.Inl (c3, g_c, reason)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____5597 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____5597
                                             (close1 x "c1 Tot")
                                       | (uu____5613,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____5638,uu____5639) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____5654 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____5654
                                        then
                                          let uu____5669 =
                                            let uu____5677 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____5677,
                                              FStar_TypeChecker_Env.trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____5669
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____5690 = try_simplify ()  in
                                match uu____5690 with
                                | FStar_Util.Inl (c,g_c,reason) ->
                                    (debug1
                                       (fun uu____5725  ->
                                          let uu____5726 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____5726);
                                     (let uu____5729 =
                                        let uu____5730 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c1 g_c2
                                           in
                                        FStar_TypeChecker_Env.conj_guard g_c
                                          uu____5730
                                         in
                                      (c, uu____5729)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____5744  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____5770 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____5770 with
                                        | (c,g_bind) ->
                                            let uu____5781 =
                                              let uu____5782 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5782 g_bind
                                               in
                                            (c, uu____5781)
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
                                        let uu____5809 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5809 with
                                        | (m,uu____5821,lift2) ->
                                            let uu____5823 =
                                              lift_comp env c22 lift2  in
                                            (match uu____5823 with
                                             | (c23,g2) ->
                                                 let uu____5834 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____5834 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____5850 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5850
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____5860 =
                                                          let uu____5865 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____5866 =
                                                            let uu____5867 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5876 =
                                                              let uu____5887
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5887]
                                                               in
                                                            uu____5867 ::
                                                              uu____5876
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5865
                                                            uu____5866
                                                           in
                                                        uu____5860
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5920 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____5920 with
                                                       | (c,g_s) ->
                                                           let uu____5935 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____5935))))
                                         in
                                      let uu____5936 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____5952 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____5952, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____5936 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____5968 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____5968
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____5977 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____5977
                                             then
                                               (debug1
                                                  (fun uu____5991  ->
                                                     let uu____5992 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____5994 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____5992 uu____5994);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____6002 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____6005 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____6005)
                                                   in
                                                if uu____6002
                                                then
                                                  let e1' =
                                                    let uu____6030 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____6030
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____6042  ->
                                                        let uu____6043 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____6045 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____6043
                                                          uu____6045);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____6060  ->
                                                        let uu____6061 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____6063 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____6061
                                                          uu____6063);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____6070 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____6070
                                                       in
                                                    let uu____6071 =
                                                      let uu____6076 =
                                                        let uu____6077 =
                                                          let uu____6078 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____6078]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____6077
                                                         in
                                                      weaken_comp uu____6076
                                                        c21 x_eq_e
                                                       in
                                                    match uu____6071 with
                                                    | (c22,g_w) ->
                                                        let uu____6103 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____6103
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____6114 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____6114))))))
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
      | uu____6131 -> g2
  
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
            (let uu____6155 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6155)
           in
        let flags =
          if should_return1
          then
            let uu____6163 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6163
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6181 =
          let uu____6182 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6182 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6195 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6195
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6203 =
                  let uu____6205 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6205  in
                (if uu____6203
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___802_6214 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___802_6214.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___802_6214.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___802_6214.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6215 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6215, g_c)
                 else
                   (let uu____6218 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6218, g_c)))
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
                   let uu____6229 =
                     let uu____6230 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6230
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6229
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6233 =
                   let uu____6238 =
                     let uu____6239 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6239
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6238  in
                 match uu____6233 with
                 | (bind_c,g_bind) ->
                     let uu____6248 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6249 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6248, uu____6249))
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
            fun uu____6285  ->
              match uu____6285 with
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
                    let uu____6297 =
                      ((let uu____6301 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6301) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6297
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6319 =
        let uu____6320 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6320  in
      FStar_Syntax_Syntax.fvar uu____6319 FStar_Syntax_Syntax.delta_constant
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
                  let uu____6370 =
                    let uu____6375 =
                      let uu____6376 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____6376 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____6375 [u_a]
                     in
                  match uu____6370 with
                  | (uu____6387,conjunction) ->
                      let uu____6389 =
                        let uu____6398 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____6413 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____6398, uu____6413)  in
                      (match uu____6389 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____6459 =
                               let uu____6461 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____6461 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____6459)
                              in
                           let uu____6465 =
                             let uu____6510 =
                               let uu____6511 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____6511.FStar_Syntax_Syntax.n  in
                             match uu____6510 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____6560) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____6592 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____6592 with
                                  | (a_b::bs1,body1) ->
                                      let uu____6664 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____6664 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____6812 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____6812)))
                             | uu____6845 ->
                                 let uu____6846 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____6846 r
                              in
                           (match uu____6465 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____6971 =
                                  let uu____6978 =
                                    let uu____6979 =
                                      let uu____6980 =
                                        let uu____6987 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____6987, a)  in
                                      FStar_Syntax_Syntax.NT uu____6980  in
                                    [uu____6979]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____6978
                                    (fun b  ->
                                       let uu____7003 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____7005 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____7007 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____7003 uu____7005 uu____7007) r
                                   in
                                (match uu____6971 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____7045 =
                                                let uu____7052 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____7052, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____7045) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____7091 =
                                           let uu____7092 =
                                             let uu____7095 =
                                               let uu____7096 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7096.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7095
                                              in
                                           uu____7092.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7091 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7107,uu____7108::is) ->
                                             let uu____7150 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7150
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7183 ->
                                             let uu____7184 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7184 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____7200 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7200)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____7205 =
                                           let uu____7206 =
                                             let uu____7209 =
                                               let uu____7210 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7210.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7209
                                              in
                                           uu____7206.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7205 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7221,uu____7222::is) ->
                                             let uu____7264 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7264
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7297 ->
                                             let uu____7298 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7298 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____7314 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7314)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____7319 =
                                         let uu____7320 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____7320.FStar_Syntax_Syntax.n  in
                                       match uu____7319 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7325,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____7380 ->
                                           let uu____7381 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____7381 r
                                        in
                                     let uu____7390 =
                                       let uu____7391 =
                                         let uu____7392 =
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
                                             uu____7392;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____7391
                                        in
                                     let uu____7415 =
                                       let uu____7416 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____7416 g_guard
                                        in
                                     (uu____7390, uu____7415))))
  
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
                fun uu____7461  ->
                  let if_then_else1 =
                    let uu____7467 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____7467 FStar_Util.must  in
                  let uu____7474 = destruct_wp_comp ct1  in
                  match uu____7474 with
                  | (uu____7485,uu____7486,wp_t) ->
                      let uu____7488 = destruct_wp_comp ct2  in
                      (match uu____7488 with
                       | (uu____7499,uu____7500,wp_e) ->
                           let wp =
                             let uu____7505 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____7506 =
                               let uu____7511 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____7512 =
                                 let uu____7513 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____7522 =
                                   let uu____7533 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____7542 =
                                     let uu____7553 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____7562 =
                                       let uu____7573 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____7573]  in
                                     uu____7553 :: uu____7562  in
                                   uu____7533 :: uu____7542  in
                                 uu____7513 :: uu____7522  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____7511
                                 uu____7512
                                in
                             uu____7506 FStar_Pervasives_Native.None
                               uu____7505
                              in
                           let uu____7622 = mk_comp ed u_a a wp []  in
                           (uu____7622, FStar_TypeChecker_Env.trivial_guard))
  
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
               fun uu____7692  ->
                 match uu____7692 with
                 | (uu____7706,eff_label,uu____7708,uu____7709) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____7722 =
          let uu____7730 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____7768  ->
                    match uu____7768 with
                    | (uu____7783,uu____7784,flags,uu____7786) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_7803  ->
                                match uu___5_7803 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____7806 -> false))))
             in
          if uu____7730
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____7722 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____7843 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____7845 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____7845
              then
                let uu____7852 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____7852, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____7859 =
                       let uu____7868 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7868]  in
                     let uu____7887 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7859 uu____7887  in
                   let kwp =
                     let uu____7893 =
                       let uu____7902 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7902]  in
                     let uu____7921 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7893 uu____7921  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7928 =
                       let uu____7929 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7929]  in
                     let uu____7948 =
                       let uu____7951 =
                         let uu____7958 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7958
                          in
                       let uu____7959 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7951 uu____7959  in
                     FStar_Syntax_Util.abs uu____7928 uu____7948
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
                   let uu____7983 =
                     should_not_inline_whole_match ||
                       (let uu____7986 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7986)
                      in
                   if uu____7983 then cthen true else cthen false  in
                 let uu____7993 =
                   FStar_List.fold_right
                     (fun uu____8046  ->
                        fun uu____8047  ->
                          match (uu____8046, uu____8047) with
                          | ((g,eff_label,uu____8101,cthen),(uu____8103,celse,g_comp))
                              ->
                              let uu____8144 =
                                let uu____8149 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____8149
                                 in
                              (match uu____8144 with
                               | (cthen1,gthen) ->
                                   let uu____8160 =
                                     let uu____8169 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____8169 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____8192 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____8193 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____8192, uu____8193, g_lift)
                                      in
                                   (match uu____8160 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          let uu____8243 =
                                            FStar_All.pipe_right md
                                              FStar_Syntax_Util.is_layered
                                             in
                                          if uu____8243
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____8277 =
                                          let uu____8282 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____8282
                                           in
                                        (match uu____8277 with
                                         | (c,g_conjunction) ->
                                             let uu____8293 =
                                               let uu____8294 =
                                                 let uu____8295 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____8295 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____8294 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____8293)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____7993 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____8329::[] -> (comp, g_comp)
                      | uu____8372 ->
                          let uu____8389 =
                            let uu____8391 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            FStar_All.pipe_right uu____8391
                              FStar_Syntax_Util.is_layered
                             in
                          if uu____8389
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
                             let uu____8404 = destruct_wp_comp comp1  in
                             match uu____8404 with
                             | (uu____8415,uu____8416,wp) ->
                                 let ite_wp =
                                   let uu____8419 =
                                     FStar_All.pipe_right md1
                                       FStar_Syntax_Util.get_wp_ite_combinator
                                      in
                                   FStar_All.pipe_right uu____8419
                                     FStar_Util.must
                                    in
                                 let wp1 =
                                   let uu____8429 =
                                     let uu____8434 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_res_t] env md1 ite_wp
                                        in
                                     let uu____8435 =
                                       let uu____8436 =
                                         FStar_Syntax_Syntax.as_arg res_t  in
                                       let uu____8445 =
                                         let uu____8456 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [uu____8456]  in
                                       uu____8436 :: uu____8445  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____8434
                                       uu____8435
                                      in
                                   uu____8429 FStar_Pervasives_Native.None
                                     wp.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____8489 =
                                   mk_comp md1 u_res_t res_t wp1
                                     bind_cases_flags
                                    in
                                 (uu____8489, g_comp))))
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
          let uu____8524 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____8524 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____8540 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____8546 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____8540 uu____8546
              else
                (let uu____8555 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____8561 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____8555 uu____8561)
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
          let uu____8586 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____8586
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____8589 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____8589
        then u_res
        else
          (let is_total =
             let uu____8596 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____8596
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____8607 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____8607 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8610 =
                    let uu____8616 =
                      let uu____8618 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____8618
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____8616)
                     in
                  FStar_Errors.raise_error uu____8610
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
      let uu____8642 = destruct_wp_comp ct  in
      match uu____8642 with
      | (u_t,t,wp) ->
          let vc =
            let uu____8661 = FStar_TypeChecker_Env.get_range env  in
            let uu____8662 =
              let uu____8667 =
                let uu____8668 =
                  let uu____8669 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____8669 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____8668
                 in
              let uu____8676 =
                let uu____8677 = FStar_Syntax_Syntax.as_arg t  in
                let uu____8686 =
                  let uu____8697 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____8697]  in
                uu____8677 :: uu____8686  in
              FStar_Syntax_Syntax.mk_Tm_app uu____8667 uu____8676  in
            uu____8662 FStar_Pervasives_Native.None uu____8661  in
          let uu____8730 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____8730)
  
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
                  let uu____8785 = FStar_TypeChecker_Env.try_lookup_lid env f
                     in
                  match uu____8785 with
                  | FStar_Pervasives_Native.Some uu____8800 ->
                      ((let uu____8818 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____8818
                        then
                          let uu____8822 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____8822
                        else ());
                       (let coercion =
                          let uu____8828 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____8828
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____8835 =
                            let uu____8836 =
                              let uu____8837 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____8837
                               in
                            (FStar_Pervasives_Native.None, uu____8836)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____8835
                           in
                        let e1 =
                          let uu____8843 =
                            let uu____8848 =
                              let uu____8849 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____8849]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____8848
                             in
                          uu____8843 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8883 =
                          let uu____8889 =
                            let uu____8891 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____8891
                             in
                          (FStar_Errors.Warning_CoercionNotFound, uu____8889)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____8883);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____8910 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____8928 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____8939 -> false 
let rec (check_erased :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> isErased) =
  fun env  ->
    fun t  ->
      let norm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Primops;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Iota]
         in
      let t1 = norm' env t  in
      let t2 = FStar_Syntax_Util.unrefine t1  in
      let uu____8963 = FStar_Syntax_Util.head_and_args t2  in
      match uu____8963 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____9008 =
              let uu____9023 =
                let uu____9024 = FStar_Syntax_Subst.compress h1  in
                uu____9024.FStar_Syntax_Syntax.n  in
              (uu____9023, args)  in
            match uu____9008 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____9071,uu____9072) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____9105) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match (uu____9126,branches),uu____9128)
                ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____9192 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____9193 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____9193 with
                               | (uu____9194,uu____9195,br_body) ->
                                   let uu____9213 =
                                     let uu____9214 =
                                       let uu____9219 =
                                         let uu____9220 =
                                           let uu____9223 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____9223
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____9220
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____9219  in
                                     FStar_All.pipe_right br_body uu____9214
                                      in
                                   (match uu____9213 with
                                    | No  -> No
                                    | uu____9234 -> Maybe))) No)
            | uu____9235 -> No  in
          r
  
let (maybe_coerce_lc :
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
        fun exp_t  ->
          let should_coerce =
            (((let uu____9287 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____9287) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9306 =
                 let uu____9307 = FStar_Syntax_Subst.compress t1  in
                 uu____9307.FStar_Syntax_Syntax.n  in
               match uu____9306 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____9312 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9322 =
                 let uu____9323 = FStar_Syntax_Subst.compress t1  in
                 uu____9323.FStar_Syntax_Syntax.n  in
               match uu____9322 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____9328 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9338 =
                 let uu____9339 = FStar_Syntax_Subst.compress t1  in
                 uu____9339.FStar_Syntax_Syntax.n  in
               match uu____9338 with
               | FStar_Syntax_Syntax.Tm_type uu____9343 -> true
               | uu____9345 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____9348 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____9348 with
             | (head1,args) ->
                 ((let uu____9398 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____9398
                   then
                     let uu____9402 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____9404 = FStar_Syntax_Print.term_to_string e  in
                     let uu____9406 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____9408 = FStar_Syntax_Print.term_to_string exp_t
                        in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____9402 uu____9404 uu____9406 uu____9408
                   else ());
                  (let mk_erased u t =
                     let uu____9426 =
                       let uu____9429 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____9429 [u]  in
                     let uu____9430 =
                       let uu____9441 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____9441]  in
                     FStar_Syntax_Util.mk_app uu____9426 uu____9430  in
                   let uu____9466 =
                     let uu____9481 =
                       let uu____9482 = FStar_Syntax_Util.un_uinst head1  in
                       uu____9482.FStar_Syntax_Syntax.n  in
                     (uu____9481, args)  in
                   match uu____9466 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____9520 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____9520 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____9560 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____9560 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____9600 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____9600 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____9640 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____9640 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____9661 ->
                       let uu____9676 =
                         let uu____9681 = check_erased env res_typ  in
                         let uu____9682 = check_erased env exp_t  in
                         (uu____9681, uu____9682)  in
                       (match uu____9676 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____9691 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____9691 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____9702 =
                                   let uu____9707 =
                                     let uu____9708 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____9708]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____9707
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____9702 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____9743 =
                              let uu____9748 =
                                let uu____9749 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____9749]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____9748
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____9743 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____9782 ->
                            (e, lc, FStar_TypeChecker_Env.trivial_guard)))))
  
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
        let uu____9817 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____9817 with
        | (hd1,args) ->
            let uu____9866 =
              let uu____9881 =
                let uu____9882 = FStar_Syntax_Subst.compress hd1  in
                uu____9882.FStar_Syntax_Syntax.n  in
              (uu____9881, args)  in
            (match uu____9866 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____9920 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _9947  -> FStar_Pervasives_Native.Some _9947)
                   uu____9920
             | uu____9948 -> FStar_Pervasives_Native.None)
  
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
          (let uu____10001 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____10001
           then
             let uu____10004 = FStar_Syntax_Print.term_to_string e  in
             let uu____10006 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____10008 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____10004 uu____10006 uu____10008
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____10018 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____10018 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____10043 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____10069 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____10069, false)
             else
               (let uu____10079 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____10079, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____10092) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____10104 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____10104
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1222_10120 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1222_10120.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1222_10120.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1222_10120.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____10127 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____10127 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____10143 =
                      let uu____10144 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____10144 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____10164 =
                            let uu____10166 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____10166 = FStar_Syntax_Util.Equal  in
                          if uu____10164
                          then
                            ((let uu____10173 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____10173
                              then
                                let uu____10177 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____10179 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____10177 uu____10179
                              else ());
                             (let uu____10184 = set_result_typ1 c  in
                              (uu____10184, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____10191 ->
                                   true
                               | uu____10199 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____10208 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____10208
                                  in
                               let lc1 =
                                 let uu____10210 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____10211 =
                                   let uu____10212 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____10212)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____10210 uu____10211
                                  in
                               ((let uu____10216 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10216
                                 then
                                   let uu____10220 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____10222 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____10224 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____10226 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____10220 uu____10222 uu____10224
                                     uu____10226
                                 else ());
                                (let uu____10231 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____10231 with
                                 | (c1,g_lc) ->
                                     let uu____10242 = set_result_typ1 c1  in
                                     let uu____10243 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____10242, uu____10243)))
                             else
                               ((let uu____10247 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10247
                                 then
                                   let uu____10251 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____10253 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____10251 uu____10253
                                 else ());
                                (let uu____10258 = set_result_typ1 c  in
                                 (uu____10258, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1259_10262 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1259_10262.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1259_10262.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1259_10262.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____10272 =
                      let uu____10273 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____10273
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____10283 =
                           let uu____10284 = FStar_Syntax_Subst.compress f1
                              in
                           uu____10284.FStar_Syntax_Syntax.n  in
                         match uu____10283 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____10291,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____10293;
                                            FStar_Syntax_Syntax.vars =
                                              uu____10294;_},uu____10295)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1275_10321 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1275_10321.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1275_10321.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1275_10321.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____10322 ->
                             let uu____10323 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____10323 with
                              | (c,g_c) ->
                                  ((let uu____10335 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____10335
                                    then
                                      let uu____10339 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____10341 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____10343 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____10345 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____10339 uu____10341 uu____10343
                                        uu____10345
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
                                        let uu____10358 =
                                          let uu____10363 =
                                            let uu____10364 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____10364]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____10363
                                           in
                                        uu____10358
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____10391 =
                                      let uu____10396 =
                                        FStar_All.pipe_left
                                          (fun _10417  ->
                                             FStar_Pervasives_Native.Some
                                               _10417)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____10418 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____10419 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____10420 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____10396
                                        uu____10418 e uu____10419 uu____10420
                                       in
                                    match uu____10391 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1293_10428 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1293_10428.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1293_10428.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____10430 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____10430
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____10433 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____10433 with
                                         | (c2,g_lc) ->
                                             ((let uu____10445 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____10445
                                               then
                                                 let uu____10449 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____10449
                                               else ());
                                              (let uu____10454 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____10454))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_10463  ->
                              match uu___6_10463 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____10466 -> []))
                       in
                    let lc1 =
                      let uu____10468 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____10468 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1309_10470 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1309_10470.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1309_10470.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1309_10470.FStar_TypeChecker_Common.implicits)
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
        let uu____10506 =
          let uu____10509 =
            let uu____10514 =
              let uu____10515 =
                let uu____10524 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____10524  in
              [uu____10515]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____10514  in
          uu____10509 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____10506  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____10547 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____10547
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____10566 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____10582 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____10599 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____10599
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____10615)::(ens,uu____10617)::uu____10618 ->
                    let uu____10661 =
                      let uu____10664 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____10664  in
                    let uu____10665 =
                      let uu____10666 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____10666  in
                    (uu____10661, uu____10665)
                | uu____10669 ->
                    let uu____10680 =
                      let uu____10686 =
                        let uu____10688 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____10688
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____10686)
                       in
                    FStar_Errors.raise_error uu____10680
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____10708)::uu____10709 ->
                    let uu____10736 =
                      let uu____10741 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____10741
                       in
                    (match uu____10736 with
                     | (us_r,uu____10773) ->
                         let uu____10774 =
                           let uu____10779 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____10779
                            in
                         (match uu____10774 with
                          | (us_e,uu____10811) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____10814 =
                                  let uu____10815 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10815
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10814
                                  us_r
                                 in
                              let as_ens =
                                let uu____10817 =
                                  let uu____10818 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10818
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10817
                                  us_e
                                 in
                              let req =
                                let uu____10822 =
                                  let uu____10827 =
                                    let uu____10828 =
                                      let uu____10839 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10839]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10828
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____10827
                                   in
                                uu____10822 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____10879 =
                                  let uu____10884 =
                                    let uu____10885 =
                                      let uu____10896 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10896]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10885
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____10884
                                   in
                                uu____10879 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____10933 =
                                let uu____10936 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____10936  in
                              let uu____10937 =
                                let uu____10938 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____10938  in
                              (uu____10933, uu____10937)))
                | uu____10941 -> failwith "Impossible"))
  
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
        (let uu____10980 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____10980
         then
           let uu____10985 = FStar_Syntax_Print.term_to_string tm  in
           let uu____10987 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____10985
             uu____10987
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
          (let uu____11046 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____11046
           then
             let uu____11051 = FStar_Syntax_Print.term_to_string tm  in
             let uu____11053 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____11051
               uu____11053
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____11064 =
      let uu____11066 =
        let uu____11067 = FStar_Syntax_Subst.compress t  in
        uu____11067.FStar_Syntax_Syntax.n  in
      match uu____11066 with
      | FStar_Syntax_Syntax.Tm_app uu____11071 -> false
      | uu____11089 -> true  in
    if uu____11064
    then t
    else
      (let uu____11094 = FStar_Syntax_Util.head_and_args t  in
       match uu____11094 with
       | (head1,args) ->
           let uu____11137 =
             let uu____11139 =
               let uu____11140 = FStar_Syntax_Subst.compress head1  in
               uu____11140.FStar_Syntax_Syntax.n  in
             match uu____11139 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____11145 -> false  in
           if uu____11137
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____11177 ->
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
          ((let uu____11224 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____11224
            then
              let uu____11227 = FStar_Syntax_Print.term_to_string e  in
              let uu____11229 = FStar_Syntax_Print.term_to_string t  in
              let uu____11231 =
                let uu____11233 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____11233
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____11227 uu____11229 uu____11231
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____11246 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____11246 with
              | (formals,uu____11262) ->
                  let n_implicits =
                    let uu____11284 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____11362  ->
                              match uu____11362 with
                              | (uu____11370,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____11377 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____11377 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____11284 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____11502 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____11502 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____11516 =
                      let uu____11522 =
                        let uu____11524 = FStar_Util.string_of_int n_expected
                           in
                        let uu____11526 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____11528 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____11524 uu____11526 uu____11528
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____11522)
                       in
                    let uu____11532 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____11516 uu____11532
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_11550 =
              match uu___7_11550 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____11593 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____11593 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _11724,uu____11711)
                           when _11724 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____11757,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____11759))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____11793 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____11793 with
                            | (v1,uu____11834,g) ->
                                ((let uu____11849 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____11849
                                  then
                                    let uu____11852 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____11852
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____11862 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____11862 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____11955 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____11955))))
                       | (uu____11982,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____12019 =
                             let uu____12032 =
                               let uu____12039 =
                                 let uu____12044 = FStar_Dyn.mkdyn env  in
                                 (uu____12044, tau)  in
                               FStar_Pervasives_Native.Some uu____12039  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____12032
                              in
                           (match uu____12019 with
                            | (v1,uu____12077,g) ->
                                ((let uu____12092 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____12092
                                  then
                                    let uu____12095 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____12095
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____12105 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____12105 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____12198 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____12198))))
                       | (uu____12225,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____12273 =
                       let uu____12300 = inst_n_binders t1  in
                       aux [] uu____12300 bs1  in
                     (match uu____12273 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____12372) -> (e, torig, guard)
                           | (uu____12403,[]) when
                               let uu____12434 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____12434 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____12436 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____12464 ->
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
            | uu____12477 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____12489 =
      let uu____12493 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____12493
        (FStar_List.map
           (fun u  ->
              let uu____12505 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____12505 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____12489 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____12533 = FStar_Util.set_is_empty x  in
      if uu____12533
      then []
      else
        (let s =
           let uu____12551 =
             let uu____12554 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____12554  in
           FStar_All.pipe_right uu____12551 FStar_Util.set_elements  in
         (let uu____12570 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____12570
          then
            let uu____12575 =
              let uu____12577 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____12577  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____12575
          else ());
         (let r =
            let uu____12586 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____12586  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____12625 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____12625
                     then
                       let uu____12630 =
                         let uu____12632 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____12632
                          in
                       let uu____12636 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____12638 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____12630 uu____12636 uu____12638
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
        let uu____12668 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____12668 FStar_Util.set_elements  in
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
        | ([],uu____12707) -> generalized_univ_names
        | (uu____12714,[]) -> explicit_univ_names
        | uu____12721 ->
            let uu____12730 =
              let uu____12736 =
                let uu____12738 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____12738
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____12736)
               in
            FStar_Errors.raise_error uu____12730 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____12760 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____12760
       then
         let uu____12765 = FStar_Syntax_Print.term_to_string t  in
         let uu____12767 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____12765 uu____12767
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____12776 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____12776
        then
          let uu____12781 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____12781
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____12790 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____12790
         then
           let uu____12795 = FStar_Syntax_Print.term_to_string t  in
           let uu____12797 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____12795 uu____12797
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
        let uu____12881 =
          let uu____12883 =
            FStar_Util.for_all
              (fun uu____12897  ->
                 match uu____12897 with
                 | (uu____12907,uu____12908,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____12883  in
        if uu____12881
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____12960 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____12960
              then
                let uu____12963 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____12963
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____12970 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____12970
               then
                 let uu____12973 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____12973
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____12991 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____12991 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____13025 =
             match uu____13025 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____13062 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____13062
                   then
                     let uu____13067 =
                       let uu____13069 =
                         let uu____13073 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____13073
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____13069
                         (FStar_String.concat ", ")
                        in
                     let uu____13121 =
                       let uu____13123 =
                         let uu____13127 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____13127
                           (FStar_List.map
                              (fun u  ->
                                 let uu____13140 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____13142 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____13140
                                   uu____13142))
                          in
                       FStar_All.pipe_right uu____13123
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____13067
                       uu____13121
                   else ());
                  (let univs2 =
                     let uu____13156 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____13168 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____13168) univs1
                       uu____13156
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____13175 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____13175
                    then
                      let uu____13180 =
                        let uu____13182 =
                          let uu____13186 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____13186
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____13182
                          (FStar_String.concat ", ")
                         in
                      let uu____13234 =
                        let uu____13236 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____13250 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____13252 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____13250
                                    uu____13252))
                           in
                        FStar_All.pipe_right uu____13236
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____13180 uu____13234
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____13273 =
             let uu____13290 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____13290  in
           match uu____13273 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____13380 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____13380
                 then ()
                 else
                   (let uu____13385 = lec_hd  in
                    match uu____13385 with
                    | (lb1,uu____13393,uu____13394) ->
                        let uu____13395 = lec2  in
                        (match uu____13395 with
                         | (lb2,uu____13403,uu____13404) ->
                             let msg =
                               let uu____13407 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____13409 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____13407 uu____13409
                                in
                             let uu____13412 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____13412))
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
                 let uu____13480 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____13480
                 then ()
                 else
                   (let uu____13485 = lec_hd  in
                    match uu____13485 with
                    | (lb1,uu____13493,uu____13494) ->
                        let uu____13495 = lec2  in
                        (match uu____13495 with
                         | (lb2,uu____13503,uu____13504) ->
                             let msg =
                               let uu____13507 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____13509 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____13507 uu____13509
                                in
                             let uu____13512 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____13512))
                  in
               let lecs1 =
                 let uu____13523 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____13576 = univs_and_uvars_of_lec this_lec  in
                        match uu____13576 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____13523 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____13681 = lec_hd  in
                   match uu____13681 with
                   | (lbname,e,c) ->
                       let uu____13691 =
                         let uu____13697 =
                           let uu____13699 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____13701 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____13703 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____13699 uu____13701 uu____13703
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____13697)
                          in
                       let uu____13707 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____13691 uu____13707
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____13726 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____13726 with
                         | FStar_Pervasives_Native.Some uu____13735 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____13743 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____13747 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____13747 with
                              | (bs,kres) ->
                                  ((let uu____13791 =
                                      let uu____13792 =
                                        let uu____13795 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____13795
                                         in
                                      uu____13792.FStar_Syntax_Syntax.n  in
                                    match uu____13791 with
                                    | FStar_Syntax_Syntax.Tm_type uu____13796
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____13800 =
                                          let uu____13802 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____13802  in
                                        if uu____13800
                                        then fail1 kres
                                        else ()
                                    | uu____13807 -> fail1 kres);
                                   (let a =
                                      let uu____13809 =
                                        let uu____13812 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _13815  ->
                                             FStar_Pervasives_Native.Some
                                               _13815) uu____13812
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____13809
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____13823 ->
                                          let uu____13832 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____13832
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
                      (fun uu____13935  ->
                         match uu____13935 with
                         | (lbname,e,c) ->
                             let uu____13981 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____14042 ->
                                   let uu____14055 = (e, c)  in
                                   (match uu____14055 with
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
                                                (fun uu____14095  ->
                                                   match uu____14095 with
                                                   | (x,uu____14101) ->
                                                       let uu____14102 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____14102)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____14120 =
                                                let uu____14122 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____14122
                                                 in
                                              if uu____14120
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
                                          let uu____14131 =
                                            let uu____14132 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____14132.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14131 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____14157 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____14157 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____14168 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____14172 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____14172, gen_tvars))
                                in
                             (match uu____13981 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize' :
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
        (let uu____14319 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____14319
         then
           let uu____14322 =
             let uu____14324 =
               FStar_List.map
                 (fun uu____14339  ->
                    match uu____14339 with
                    | (lb,uu____14348,uu____14349) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____14324 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____14322
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____14375  ->
                match uu____14375 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____14404 = gen env is_rec lecs  in
           match uu____14404 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____14503  ->
                       match uu____14503 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____14565 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____14565
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____14613  ->
                           match uu____14613 with
                           | (l,us,e,c,gvs) ->
                               let uu____14647 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____14649 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____14651 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____14653 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____14655 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____14647 uu____14649 uu____14651
                                 uu____14653 uu____14655))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____14700  ->
                match uu____14700 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____14744 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____14744, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
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
        let uu____14799 =
          let uu____14803 =
            let uu____14805 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____14805  in
          FStar_Pervasives_Native.Some uu____14803  in
        FStar_Profiling.profile
          (fun uu____14822  -> generalize' env is_rec lecs) uu____14799
          "FStar.TypeChecker.Util.generalize"
  
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
              (let uu____14882 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____14882 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____14888 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _14891  -> FStar_Pervasives_Native.Some _14891)
                     uu____14888)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1766_14911 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1766_14911.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1766_14911.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____14912 -> e2  in
          let uu____14913 = maybe_coerce_lc env1 e lc t2  in
          match uu____14913 with
          | (e1,lc1,g_c) ->
              let uu____14929 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____14929 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14938 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____14944 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____14938 uu____14944
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____14953 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____14953
                     then
                       let uu____14958 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____14958
                     else ());
                    (let uu____14964 = decorate e1 t2  in
                     let uu____14965 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (uu____14964, lc1, uu____14965))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____14993 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____14993
         then
           let uu____14996 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____14996
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____15010 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____15010 with
         | (c,g_c) ->
             let uu____15022 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____15022
             then
               let uu____15030 =
                 let uu____15032 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____15032  in
               (uu____15030, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____15040 =
                    let uu____15041 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____15041
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____15040
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____15042 = check_trivial_precondition env c1  in
                match uu____15042 with
                | (ct,vc,g_pre) ->
                    ((let uu____15058 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____15058
                      then
                        let uu____15063 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____15063
                      else ());
                     (let uu____15068 =
                        let uu____15070 =
                          let uu____15071 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____15071  in
                        discharge uu____15070  in
                      let uu____15072 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____15068, uu____15072)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_15106 =
        match uu___8_15106 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____15116)::[] -> f fst1
        | uu____15141 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____15153 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____15153
          (fun _15154  -> FStar_TypeChecker_Common.NonTrivial _15154)
         in
      let op_or_e e =
        let uu____15165 =
          let uu____15166 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____15166  in
        FStar_All.pipe_right uu____15165
          (fun _15169  -> FStar_TypeChecker_Common.NonTrivial _15169)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _15176  -> FStar_TypeChecker_Common.NonTrivial _15176)
         in
      let op_or_t t =
        let uu____15187 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____15187
          (fun _15190  -> FStar_TypeChecker_Common.NonTrivial _15190)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _15197  -> FStar_TypeChecker_Common.NonTrivial _15197)
         in
      let short_op_ite uu___9_15203 =
        match uu___9_15203 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____15213)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____15240)::[] ->
            let uu____15281 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____15281
              (fun _15282  -> FStar_TypeChecker_Common.NonTrivial _15282)
        | uu____15283 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____15295 =
          let uu____15303 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____15303)  in
        let uu____15311 =
          let uu____15321 =
            let uu____15329 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____15329)  in
          let uu____15337 =
            let uu____15347 =
              let uu____15355 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____15355)  in
            let uu____15363 =
              let uu____15373 =
                let uu____15381 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____15381)  in
              let uu____15389 =
                let uu____15399 =
                  let uu____15407 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____15407)  in
                [uu____15399; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____15373 :: uu____15389  in
            uu____15347 :: uu____15363  in
          uu____15321 :: uu____15337  in
        uu____15295 :: uu____15311  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____15469 =
            FStar_Util.find_map table
              (fun uu____15484  ->
                 match uu____15484 with
                 | (x,mk1) ->
                     let uu____15501 = FStar_Ident.lid_equals x lid  in
                     if uu____15501
                     then
                       let uu____15506 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____15506
                     else FStar_Pervasives_Native.None)
             in
          (match uu____15469 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____15510 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____15518 =
      let uu____15519 = FStar_Syntax_Util.un_uinst l  in
      uu____15519.FStar_Syntax_Syntax.n  in
    match uu____15518 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____15524 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____15560)::uu____15561 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____15580 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____15589,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____15590))::uu____15591 -> bs
      | uu____15609 ->
          let uu____15610 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____15610 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____15614 =
                 let uu____15615 = FStar_Syntax_Subst.compress t  in
                 uu____15615.FStar_Syntax_Syntax.n  in
               (match uu____15614 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____15619) ->
                    let uu____15640 =
                      FStar_Util.prefix_until
                        (fun uu___10_15680  ->
                           match uu___10_15680 with
                           | (uu____15688,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____15689)) ->
                               false
                           | uu____15694 -> true) bs'
                       in
                    (match uu____15640 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____15730,uu____15731) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____15803,uu____15804) ->
                         let uu____15877 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____15897  ->
                                   match uu____15897 with
                                   | (x,uu____15906) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____15877
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____15955  ->
                                     match uu____15955 with
                                     | (x,i) ->
                                         let uu____15974 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____15974, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____15985 -> bs))
  
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
            let uu____16014 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____16014
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
          let uu____16045 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____16045
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
        (let uu____16088 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____16088
         then
           ((let uu____16093 = FStar_Ident.text_of_lid lident  in
             d uu____16093);
            (let uu____16095 = FStar_Ident.text_of_lid lident  in
             let uu____16097 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____16095 uu____16097))
         else ());
        (let fv =
           let uu____16103 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____16103
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
         let uu____16115 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1927_16117 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1927_16117.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1927_16117.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1927_16117.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1927_16117.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___1927_16117.FStar_Syntax_Syntax.sigopts)
           }), uu____16115))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_16135 =
        match uu___11_16135 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16138 -> false  in
      let reducibility uu___12_16146 =
        match uu___12_16146 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____16153 -> false  in
      let assumption uu___13_16161 =
        match uu___13_16161 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____16165 -> false  in
      let reification uu___14_16173 =
        match uu___14_16173 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____16176 -> true
        | uu____16178 -> false  in
      let inferred uu___15_16186 =
        match uu___15_16186 with
        | FStar_Syntax_Syntax.Discriminator uu____16188 -> true
        | FStar_Syntax_Syntax.Projector uu____16190 -> true
        | FStar_Syntax_Syntax.RecordType uu____16196 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____16206 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____16219 -> false  in
      let has_eq uu___16_16227 =
        match uu___16_16227 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____16231 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____16310 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16317 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____16350 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____16350))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____16381 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____16381
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
           | FStar_Syntax_Syntax.Sig_bundle uu____16401 ->
               let uu____16410 =
                 let uu____16412 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_16418  ->
                           match uu___17_16418 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____16421 -> false))
                    in
                 Prims.op_Negation uu____16412  in
               if uu____16410
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____16428 -> ()
           | uu____16435 ->
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
      let uu____16449 =
        let uu____16451 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_16457  ->
                  match uu___18_16457 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____16460 -> false))
           in
        FStar_All.pipe_right uu____16451 Prims.op_Negation  in
      if uu____16449
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____16481 =
            let uu____16487 =
              let uu____16489 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____16489 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____16487)  in
          FStar_Errors.raise_error uu____16481 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____16507 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____16515 =
            let uu____16517 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____16517  in
          if uu____16515 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____16528),uu____16529) ->
              ((let uu____16541 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____16541
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____16550 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____16550
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____16561 ->
              ((let uu____16571 =
                  let uu____16573 =
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
                  Prims.op_Negation uu____16573  in
                if uu____16571 then err'1 () else ());
               (let uu____16583 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_16589  ->
                           match uu___19_16589 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____16592 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____16583
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____16598 ->
              let uu____16605 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____16605 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____16613 ->
              let uu____16620 =
                let uu____16622 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____16622  in
              if uu____16620 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____16632 ->
              let uu____16633 =
                let uu____16635 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____16635  in
              if uu____16633 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16645 ->
              let uu____16658 =
                let uu____16660 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____16660  in
              if uu____16658 then err'1 () else ()
          | uu____16670 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____16709 =
          let uu____16710 = FStar_Syntax_Subst.compress t1  in
          uu____16710.FStar_Syntax_Syntax.n  in
        match uu____16709 with
        | FStar_Syntax_Syntax.Tm_arrow uu____16714 ->
            let uu____16729 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____16729 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____16762;
               FStar_Syntax_Syntax.index = uu____16763;
               FStar_Syntax_Syntax.sort = t2;_},uu____16765)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____16774) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____16800) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____16806 -> false
      
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
        (let uu____16816 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____16816
         then
           let uu____16821 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____16821
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
                  let uu____16886 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____16886 r  in
                let uu____16896 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____16896 with
                | (uu____16905,signature) ->
                    let uu____16907 =
                      let uu____16908 = FStar_Syntax_Subst.compress signature
                         in
                      uu____16908.FStar_Syntax_Syntax.n  in
                    (match uu____16907 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16916) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____16964 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____16979 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____16981 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____16979 eff_name.FStar_Ident.str
                                       uu____16981) r
                                 in
                              (match uu____16964 with
                               | (is,g) ->
                                   let uu____16994 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____16996 =
                                             let uu____16997 =
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
                                                 = uu____16997;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____16996
                                            in
                                         let uu____17016 =
                                           let uu____17023 =
                                             let uu____17024 =
                                               let uu____17039 =
                                                 let uu____17048 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____17048]  in
                                               (uu____17039, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____17024
                                              in
                                           FStar_Syntax_Syntax.mk uu____17023
                                            in
                                         uu____17016
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____17079 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____17079
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____17088 =
                                           let uu____17093 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____17093
                                            in
                                         uu____17088
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____16994, g))
                          | uu____17102 -> fail1 signature)
                     | uu____17103 -> fail1 signature)
  
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
            let uu____17134 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____17134
              (fun ed  ->
                 let uu____17142 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____17142 u a_tm)
  
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
              let uu____17178 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____17178 with
              | (uu____17183,sig_tm) ->
                  let fail1 t =
                    let uu____17191 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____17191 r  in
                  let uu____17197 =
                    let uu____17198 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____17198.FStar_Syntax_Syntax.n  in
                  (match uu____17197 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____17202) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____17225)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____17247 -> fail1 sig_tm)
                   | uu____17248 -> fail1 sig_tm)
  
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
          (let uu____17279 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____17279
           then
             let uu____17284 = FStar_Syntax_Print.comp_to_string c  in
             let uu____17286 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____17284 uu____17286
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____17293 =
             let uu____17304 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____17305 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____17304, (ct.FStar_Syntax_Syntax.result_typ), uu____17305)
              in
           match uu____17293 with
           | (u,a,c_is) ->
               let uu____17353 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____17353 with
                | (uu____17362,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____17373 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____17375 = FStar_Ident.string_of_lid tgt  in
                      let uu____17377 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____17373 uu____17375 s uu____17377
                       in
                    let uu____17380 =
                      let uu____17413 =
                        let uu____17414 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____17414.FStar_Syntax_Syntax.n  in
                      match uu____17413 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____17478 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____17478 with
                           | (a_b::bs1,c2) ->
                               let uu____17538 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____17600 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____17538, uu____17600))
                      | uu____17627 ->
                          let uu____17628 =
                            let uu____17634 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____17634)
                             in
                          FStar_Errors.raise_error uu____17628 r
                       in
                    (match uu____17380 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____17752 =
                           let uu____17759 =
                             let uu____17760 =
                               let uu____17761 =
                                 let uu____17768 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____17768, a)  in
                               FStar_Syntax_Syntax.NT uu____17761  in
                             [uu____17760]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____17759
                             (fun b  ->
                                let uu____17785 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____17787 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____17789 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____17791 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____17785 uu____17787 uu____17789
                                  uu____17791) r
                            in
                         (match uu____17752 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____17805 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____17805
                                then
                                  let uu____17810 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____17819 =
                                             let uu____17821 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____17821
                                              in
                                           Prims.op_Hat s uu____17819) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____17810
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____17852 =
                                           let uu____17859 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____17859, t)  in
                                         FStar_Syntax_Syntax.NT uu____17852)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____17878 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____17878
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____17884 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____17884
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____17893 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____17893)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____17897 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____17897 r
                                   in
                                let c1 =
                                  let uu____17900 =
                                    let uu____17901 =
                                      let uu____17912 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____17912
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____17901;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____17900  in
                                (let uu____17932 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____17932
                                 then
                                   let uu____17937 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____17937
                                 else ());
                                (let uu____17942 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____17942))))))))
  
let lift_tf_layered_effect_term :
  'Auu____17956 .
    'Auu____17956 ->
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
              let uu____17985 =
                let uu____17990 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____17990
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____17985 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____18033 =
                let uu____18034 =
                  let uu____18037 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____18037
                    FStar_Syntax_Subst.compress
                   in
                uu____18034.FStar_Syntax_Syntax.n  in
              match uu____18033 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____18060::bs,uu____18062)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____18102 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____18102
                    FStar_Pervasives_Native.fst
              | uu____18208 ->
                  let uu____18209 =
                    let uu____18215 =
                      let uu____18217 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____18217
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____18215)  in
                  FStar_Errors.raise_error uu____18209
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____18244 = FStar_Syntax_Syntax.as_arg a  in
              let uu____18253 =
                let uu____18264 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____18300  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____18307 =
                  let uu____18318 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____18318]  in
                FStar_List.append uu____18264 uu____18307  in
              uu____18244 :: uu____18253  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____18389 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____18389 with
        | (uu____18394,t) ->
            let err n1 =
              let uu____18404 =
                let uu____18410 =
                  let uu____18412 = FStar_Ident.string_of_lid datacon  in
                  let uu____18414 = FStar_Util.string_of_int n1  in
                  let uu____18416 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____18412 uu____18414 uu____18416
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____18410)
                 in
              let uu____18420 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____18404 uu____18420  in
            let uu____18421 =
              let uu____18422 = FStar_Syntax_Subst.compress t  in
              uu____18422.FStar_Syntax_Syntax.n  in
            (match uu____18421 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18426) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____18481  ->
                           match uu____18481 with
                           | (uu____18489,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____18498 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____18530 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____18530
                      FStar_Pervasives_Native.fst)
             | uu____18541 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____18554 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____18554
      then
        let uu____18557 =
          let uu____18570 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____18570
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____18557;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18605 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____18605 with
           | (uu____18614,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____18633 =
                 let uu____18634 =
                   let uu___2294_18635 = ct  in
                   let uu____18636 =
                     let uu____18647 =
                       let uu____18656 =
                         let uu____18657 =
                           let uu____18664 =
                             let uu____18665 =
                               let uu____18682 =
                                 let uu____18693 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____18693; wp]  in
                               (lift_t, uu____18682)  in
                             FStar_Syntax_Syntax.Tm_app uu____18665  in
                           FStar_Syntax_Syntax.mk uu____18664  in
                         uu____18657 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____18656
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____18647]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2294_18635.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2294_18635.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____18636;
                     FStar_Syntax_Syntax.flags =
                       (uu___2294_18635.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____18634  in
               (uu____18633, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____18793 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____18793 with
           | (uu____18800,lift_t) ->
               let uu____18802 =
                 let uu____18809 =
                   let uu____18810 =
                     let uu____18827 =
                       let uu____18838 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____18847 =
                         let uu____18858 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____18867 =
                           let uu____18878 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____18878]  in
                         uu____18858 :: uu____18867  in
                       uu____18838 :: uu____18847  in
                     (lift_t, uu____18827)  in
                   FStar_Syntax_Syntax.Tm_app uu____18810  in
                 FStar_Syntax_Syntax.mk uu____18809  in
               uu____18802 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____18931 =
           let uu____18944 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____18944 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____18931;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____18980  ->
                        fun uu____18981  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____19004 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____19004
  
let (update_env_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ty  ->
            FStar_TypeChecker_Env.add_polymonadic_bind env m n1 p
              (fun env1  ->
                 fun c1  ->
                   fun bv_opt  ->
                     fun c2  ->
                       fun flags  ->
                         fun r  ->
                           mk_indexed_bind env1 m n1 p ty c1 bv_opt c2 flags
                             r)
  