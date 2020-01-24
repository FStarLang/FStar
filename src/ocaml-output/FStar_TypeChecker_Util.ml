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
    fun l1_in  ->
      fun l2_in  ->
        let uu____1101 =
          let uu____1106 = FStar_TypeChecker_Env.norm_eff_name env l1_in  in
          let uu____1107 = FStar_TypeChecker_Env.norm_eff_name env l2_in  in
          (uu____1106, uu____1107)  in
        match uu____1101 with
        | (l1,l2) ->
            let uu____1110 = FStar_TypeChecker_Env.join_opt env l1 l2  in
            (match uu____1110 with
             | FStar_Pervasives_Native.Some (m,uu____1120,uu____1121) -> m
             | FStar_Pervasives_Native.None  ->
                 let uu____1134 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2
                    in
                 (match uu____1134 with
                  | FStar_Pervasives_Native.Some (m,uu____1148) -> m
                  | FStar_Pervasives_Native.None  ->
                      let uu____1181 =
                        let uu____1187 =
                          let uu____1189 =
                            FStar_Syntax_Print.lid_to_string l1_in  in
                          let uu____1191 =
                            FStar_Syntax_Print.lid_to_string l2_in  in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____1189
                            uu____1191
                           in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____1187)
                         in
                      FStar_Errors.raise_error uu____1181
                        env.FStar_TypeChecker_Env.range))
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1211 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____1211
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
            let uu____1266 =
              FStar_TypeChecker_Env.join env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____1266 with
            | (m,lift1,lift2) ->
                let uu____1284 = lift_comp env c11 lift1  in
                (match uu____1284 with
                 | (c12,g1) ->
                     let uu____1299 =
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
                          let uu____1338 = lift_comp env_x c21 lift2  in
                          match uu____1338 with
                          | (c22,g2) ->
                              let uu____1349 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____1349))
                        in
                     (match uu____1299 with
                      | (c22,g2) ->
                          let uu____1372 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (m, c12, c22, uu____1372)))
  
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
            let uu____1433 =
              let uu____1434 =
                let uu____1445 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1445]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1434;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1433
  
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
          let uu____1529 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____1529
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1541 =
      let uu____1542 = FStar_Syntax_Subst.compress t  in
      uu____1542.FStar_Syntax_Syntax.n  in
    match uu____1541 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1546 -> true
    | uu____1562 -> false
  
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
              let uu____1632 =
                let uu____1634 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____1634  in
              if uu____1632
              then f
              else (let uu____1641 = reason1 ()  in label uu____1641 r f)
  
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
            let uu___256_1662 = g  in
            let uu____1663 =
              let uu____1664 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1664  in
            {
              FStar_TypeChecker_Common.guard_f = uu____1663;
              FStar_TypeChecker_Common.deferred =
                (uu___256_1662.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___256_1662.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___256_1662.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____1685 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____1685
        then c
        else
          (let uu____1690 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____1690
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____1732 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____1732 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____1760 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____1760]  in
                       let us =
                         let uu____1782 =
                           let uu____1785 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____1785]  in
                         u_res :: uu____1782  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____1791 =
                         let uu____1796 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____1797 =
                           let uu____1798 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____1807 =
                             let uu____1818 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____1827 =
                               let uu____1838 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____1838]  in
                             uu____1818 :: uu____1827  in
                           uu____1798 :: uu____1807  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1796 uu____1797
                          in
                       uu____1791 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____1880 = destruct_wp_comp c1  in
              match uu____1880 with
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
                let uu____1920 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____1920
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
                  let uu____1970 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____1970
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_1983  ->
            match uu___0_1983 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____1986 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____2011 =
            let uu____2014 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____2014 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____2011
            (fun c  ->
               (let uu____2070 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____2070) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____2074 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____2074)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____2085 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2085 with
                | (head1,uu____2102) ->
                    let uu____2123 =
                      let uu____2124 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2124.FStar_Syntax_Syntax.n  in
                    (match uu____2123 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2129 =
                           let uu____2131 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2131
                            in
                         Prims.op_Negation uu____2129
                     | uu____2132 -> true)))
              &&
              (let uu____2135 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2135)
  
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
            let uu____2163 =
              let uu____2165 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2165  in
            if uu____2163
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2172 = FStar_Syntax_Util.is_unit t  in
               if uu____2172
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
                    let uu____2181 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2181
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2186 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2186 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let ret_wp =
                             FStar_All.pipe_right m
                               FStar_Syntax_Util.get_return_vc_combinator
                              in
                           let uu____2197 =
                             let uu____2198 =
                               let uu____2203 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m ret_wp
                                  in
                               let uu____2204 =
                                 let uu____2205 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2214 =
                                   let uu____2225 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2225]  in
                                 uu____2205 :: uu____2214  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2203
                                 uu____2204
                                in
                             uu____2198 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env uu____2197)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2259 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2259
           then
             let uu____2264 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2266 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2268 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2264 uu____2266 uu____2268
           else ());
          c
  
let (effect_args_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool -> FStar_Range.range -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr  ->
    fun is_layered1  ->
      fun r  ->
        let err uu____2302 =
          let uu____2303 =
            let uu____2309 =
              let uu____2311 = FStar_Syntax_Print.term_to_string repr  in
              let uu____2313 = FStar_Util.string_of_bool is_layered1  in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____2311 uu____2313
               in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____2309)  in
          FStar_Errors.raise_error uu____2303 r  in
        let repr1 = FStar_Syntax_Subst.compress repr  in
        if is_layered1
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu____2325,uu____2326::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu____2394 -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu____2399,c) ->
               let uu____2421 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ
                  in
               FStar_All.pipe_right uu____2421
                 (fun ct  ->
                    FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                      (FStar_List.map FStar_Pervasives_Native.fst))
           | uu____2456 -> err ())
  
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
                      (let uu____2525 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____2525
                       then
                         let uu____2530 =
                           let uu____2532 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____2532  in
                         let uu____2533 =
                           let uu____2535 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____2535  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____2530 uu____2533
                       else ());
                      (let uu____2539 =
                         let uu____2546 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____2547 =
                           FStar_TypeChecker_Env.get_effect_decl env n1  in
                         let uu____2548 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____2546, uu____2547, uu____2548)  in
                       match uu____2539 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____2556 =
                             let uu____2567 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____2568 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____2567,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____2568)
                              in
                           (match uu____2556 with
                            | (u1,t1,is1) ->
                                let uu____2602 =
                                  let uu____2613 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____2614 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____2613,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____2614)
                                   in
                                (match uu____2602 with
                                 | (u2,t2,is2) ->
                                     let uu____2648 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____2648 with
                                      | (uu____2657,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____2672 =
                                              let uu____2674 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____2674 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____2672)
                                             in
                                          let uu____2678 =
                                            let uu____2723 =
                                              let uu____2724 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____2724.FStar_Syntax_Syntax.n
                                               in
                                            match uu____2723 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____2800 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____2800 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____2885 =
                                                       let uu____2912 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2912
                                                         (fun uu____2997  ->
                                                            match uu____2997
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____3078
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____3091
                                                                  =
                                                                  let uu____3098
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____3098
                                                                   in
                                                                (l1,
                                                                  uu____3078,
                                                                  uu____3091))
                                                        in
                                                     (match uu____2885 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          let uu____3226 =
                                                            FStar_Syntax_Util.comp_to_comp_typ
                                                              c1
                                                             in
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b,
                                                            uu____3226)))
                                            | uu____3259 ->
                                                let uu____3260 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____3260 r1
                                             in
                                          (match uu____2678 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_ct)
                                               ->
                                               let uu____3385 =
                                                 let uu____3392 =
                                                   let uu____3393 =
                                                     let uu____3394 =
                                                       let uu____3401 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____3401, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____3394
                                                      in
                                                   let uu____3412 =
                                                     let uu____3415 =
                                                       let uu____3416 =
                                                         let uu____3423 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____3423, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____3416
                                                        in
                                                     [uu____3415]  in
                                                   uu____3393 :: uu____3412
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____3392
                                                   (fun b1  ->
                                                      let uu____3438 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____3440 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s:bind at %s"
                                                        uu____3438 ""
                                                        uu____3440) r1
                                                  in
                                               (match uu____3385 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____3478 =
                                                               let uu____3485
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____3485,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____3478)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____3512 =
                                                          let uu____3515 =
                                                            let uu____3516 =
                                                              let uu____3517
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____3517.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____3516
                                                             in
                                                          let uu____3526 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____3515
                                                            uu____3526 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3512
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst1))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____3539
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____3539)
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
                                                        let uu____3558 =
                                                          let uu____3559 =
                                                            let uu____3562 =
                                                              let uu____3563
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____3563.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____3562
                                                             in
                                                          uu____3559.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____3558 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____3596 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____3596
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____3606
                                                                    =
                                                                    let uu____3613
                                                                    =
                                                                    let uu____3614
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____3614
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____3635
                                                                    =
                                                                    let uu____3638
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3638
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____3613,
                                                                    uu____3635)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____3606
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____3652
                                                                   =
                                                                   let uu____3655
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____3656
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____3655
                                                                    uu____3656
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____3652
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)))
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____3675 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____3683
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____3683)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3675
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let is =
                                                      let uu____3699 =
                                                        let uu____3702 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        let uu____3703 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed
                                                           in
                                                        effect_args_from_repr
                                                          uu____3702
                                                          uu____3703 r1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3699
                                                        (FStar_List.map
                                                           (FStar_Syntax_Subst.subst
                                                              subst1))
                                                       in
                                                    let c =
                                                      let uu____3710 =
                                                        let uu____3711 =
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
                                                            = uu____3711;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____3710
                                                       in
                                                    ((let uu____3731 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____3731
                                                      then
                                                        let uu____3736 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____3736
                                                      else ());
                                                     (let uu____3741 =
                                                        FStar_TypeChecker_Env.conj_guards
                                                          [g_uvars;
                                                          f_guard;
                                                          g_guard]
                                                         in
                                                      (c, uu____3741)))))))))
  
let (mk_wp_bind :
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
                let uu____3786 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____3812 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____3812 with
                  | (a,kwp) ->
                      let uu____3843 = destruct_wp_comp ct1  in
                      let uu____3850 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____3843, uu____3850)
                   in
                match uu____3786 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____3903 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____3903]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____3923 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3923]
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
                      let uu____3970 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____3979 =
                        let uu____3990 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____3999 =
                          let uu____4010 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____4019 =
                            let uu____4030 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____4039 =
                              let uu____4050 =
                                let uu____4059 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____4059  in
                              [uu____4050]  in
                            uu____4030 :: uu____4039  in
                          uu____4010 :: uu____4019  in
                        uu____3990 :: uu____3999  in
                      uu____3970 :: uu____3979  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____4112 =
                        let uu____4117 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____4117 wp_args  in
                      uu____4112 FStar_Pervasives_Native.None
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
              let uu____4165 =
                let uu____4170 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____4171 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____4170, uu____4171)  in
              match uu____4165 with
              | (ct1,ct2) ->
                  let uu____4178 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____4178 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____4229 = lift_comps env c1 c2 b true  in
                       (match uu____4229 with
                        | (m,c11,c21,g_lift) ->
                            let uu____4247 =
                              let uu____4252 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____4253 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____4252, uu____4253)  in
                            (match uu____4247 with
                             | (ct11,ct21) ->
                                 let uu____4260 =
                                   let uu____4265 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____4265
                                   then
                                     let bind_t =
                                       let uu____4273 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____4273
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____4276 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____4276,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____4260 with
                                  | (c,g_bind) ->
                                      let uu____4283 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____4283)))))
  
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
            let uu____4319 =
              let uu____4320 =
                let uu____4331 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____4331]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____4320;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4319  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____4376 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_4382  ->
              match uu___1_4382 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4385 -> false))
       in
    if uu____4376
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_4397  ->
              match uu___2_4397 with
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
        let uu____4425 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4425
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____4436 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____4436  in
           let pure_assume_wp1 =
             let uu____4441 = FStar_TypeChecker_Env.get_range env  in
             let uu____4442 =
               let uu____4447 =
                 let uu____4448 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____4448]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____4447  in
             uu____4442 FStar_Pervasives_Native.None uu____4441  in
           let uu____4481 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____4481)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4509 =
          let uu____4510 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____4510 with
          | (c,g_c) ->
              let uu____4521 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4521
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____4535 = weaken_comp env c f1  in
                     (match uu____4535 with
                      | (c1,g_w) ->
                          let uu____4546 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____4546)))
           in
        let uu____4547 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____4547 weaken
  
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
                 let uu____4604 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____4604  in
               let pure_assert_wp1 =
                 let uu____4609 =
                   let uu____4614 =
                     let uu____4615 =
                       let uu____4624 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____4624
                        in
                     [uu____4615]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____4614
                    in
                 uu____4609 FStar_Pervasives_Native.None r  in
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
       (let uu____4716 = FStar_Options.debug_any ()  in
        if uu____4716
        then
          let uu____4719 = FStar_Util.string_of_int n1  in
          let uu____4721 =
            let uu____4723 =
              let uu____4725 = FStar_Util.time_diff start fin  in
              FStar_Pervasives_Native.snd uu____4725  in
            FStar_Util.string_of_int uu____4723  in
          FStar_Util.print2 "Simplify_guard %s in %s ms\n" uu____4719
            uu____4721
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
            let uu____4780 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____4780
            then (lc, g0)
            else
              (let flags =
                 let uu____4792 =
                   let uu____4800 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____4800
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4792 with
                 | (maybe_trivial_post,flags) ->
                     let uu____4830 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_4838  ->
                               match uu___3_4838 with
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
                               | uu____4841 -> []))
                        in
                     FStar_List.append flags uu____4830
                  in
               let strengthen uu____4851 =
                 let uu____4852 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____4852 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____4871 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____4871 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____4878 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4878
                              then
                                let uu____4882 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____4884 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____4882 uu____4884
                              else ());
                             (let uu____4889 =
                                strengthen_comp env reason c f flags  in
                              match uu____4889 with
                              | (c1,g_s) ->
                                  let uu____4900 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____4900))))
                  in
               let uu____4901 =
                 let uu____4902 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____4902
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____4901,
                 (let uu___595_4904 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___595_4904.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___595_4904.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___595_4904.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_4913  ->
            match uu___4_4913 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4917 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____4946 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4946
          then e
          else
            (let uu____4953 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4956 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4956)
                in
             if uu____4953
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
                | uu____5026 -> false  in
              if is_unit1
              then
                let uu____5033 =
                  let uu____5035 =
                    let uu____5036 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____5036
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____5035
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____5033
                 then
                   let uu____5045 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____5045 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____5089 =
                           let uu____5092 =
                             let uu____5093 =
                               let uu____5100 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____5100, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____5093  in
                           [uu____5092]  in
                         FStar_Syntax_Subst.subst uu____5089 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____5113 = close_wp_comp env [x] c  in
                    (uu____5113, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____5116 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____5144  ->
            match uu____5144 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5164 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5164 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5177 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5177
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____5187 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____5187
                       then
                         let uu____5192 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____5192
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5199 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____5199
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5208 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____5208
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5215 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5215
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____5231 =
                  let uu____5232 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5232
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____5240 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____5240, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____5243 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____5243 with
                     | (c1,g_c1) ->
                         let uu____5254 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____5254 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____5274  ->
                                    let uu____5275 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____5277 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____5282 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____5275 uu____5277 uu____5282);
                               (let aux uu____5300 =
                                  let uu____5301 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____5301
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____5332
                                        ->
                                        let uu____5333 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____5333
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____5365 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____5365
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____5412 =
                                  let aux_with_trivial_guard uu____5442 =
                                    let uu____5443 = aux ()  in
                                    match uu____5443 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c,
                                            FStar_TypeChecker_Env.trivial_guard,
                                            reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____5501 =
                                    let uu____5503 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____5503  in
                                  if uu____5501
                                  then
                                    let uu____5519 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____5519
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           FStar_TypeChecker_Env.trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____5546 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____5546))
                                  else
                                    (let uu____5563 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____5563
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___694_5609 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___694_5609.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___694_5609.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____5610 =
                                           maybe_capture_unit_refinement env
                                             x1.FStar_Syntax_Syntax.sort x1 c
                                            in
                                         match uu____5610 with
                                         | (c3,g_c) ->
                                             FStar_Util.Inl (c3, g_c, reason)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____5668 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____5668
                                             (close1 x "c1 Tot")
                                       | (uu____5684,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____5709,uu____5710) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____5725 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____5725
                                        then
                                          let uu____5740 =
                                            let uu____5748 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____5748,
                                              FStar_TypeChecker_Env.trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____5740
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____5761 = try_simplify ()  in
                                match uu____5761 with
                                | FStar_Util.Inl (c,g_c,reason) ->
                                    (debug1
                                       (fun uu____5796  ->
                                          let uu____5797 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____5797);
                                     (let uu____5800 =
                                        let uu____5801 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c1 g_c2
                                           in
                                        FStar_TypeChecker_Env.conj_guard g_c
                                          uu____5801
                                         in
                                      (c, uu____5800)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____5815  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____5841 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____5841 with
                                        | (c,g_bind) ->
                                            let uu____5852 =
                                              let uu____5853 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____5853 g_bind
                                               in
                                            (c, uu____5852)
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
                                        let uu____5880 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____5880 with
                                        | (m,uu____5892,lift2) ->
                                            let uu____5894 =
                                              lift_comp env c22 lift2  in
                                            (match uu____5894 with
                                             | (c23,g2) ->
                                                 let uu____5905 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____5905 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____5921 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5921
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____5931 =
                                                          let uu____5936 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____5937 =
                                                            let uu____5938 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____5947 =
                                                              let uu____5958
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____5958]
                                                               in
                                                            uu____5938 ::
                                                              uu____5947
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____5936
                                                            uu____5937
                                                           in
                                                        uu____5931
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____5991 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____5991 with
                                                       | (c,g_s) ->
                                                           let uu____6006 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____6006))))
                                         in
                                      let uu____6007 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____6023 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____6023, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____6007 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____6039 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____6039
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____6048 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____6048
                                             then
                                               (debug1
                                                  (fun uu____6062  ->
                                                     let uu____6063 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____6065 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____6063 uu____6065);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____6073 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____6076 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____6076)
                                                   in
                                                if uu____6073
                                                then
                                                  let e1' =
                                                    let uu____6101 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____6101
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____6113  ->
                                                        let uu____6114 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____6116 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____6114
                                                          uu____6116);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____6131  ->
                                                        let uu____6132 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____6134 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____6132
                                                          uu____6134);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____6141 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____6141
                                                       in
                                                    let uu____6142 =
                                                      let uu____6147 =
                                                        let uu____6148 =
                                                          let uu____6149 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____6149]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____6148
                                                         in
                                                      weaken_comp uu____6147
                                                        c21 x_eq_e
                                                       in
                                                    match uu____6142 with
                                                    | (c22,g_w) ->
                                                        let uu____6174 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____6174
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____6185 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____6185))))))
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
      | uu____6202 -> g2
  
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
            (let uu____6226 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____6226)
           in
        let flags =
          if should_return1
          then
            let uu____6234 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____6234
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____6252 =
          let uu____6253 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____6253 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____6266 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____6266
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____6274 =
                  let uu____6276 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____6276  in
                (if uu____6274
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___813_6285 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___813_6285.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___813_6285.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___813_6285.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____6286 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____6286, g_c)
                 else
                   (let uu____6289 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____6289, g_c)))
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
                   let uu____6300 =
                     let uu____6301 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____6301
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____6300
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____6304 =
                   let uu____6309 =
                     let uu____6310 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____6310
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____6309  in
                 match uu____6304 with
                 | (bind_c,g_bind) ->
                     let uu____6319 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____6320 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____6319, uu____6320))
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
            fun uu____6356  ->
              match uu____6356 with
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
                    let uu____6368 =
                      ((let uu____6372 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6372) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6368
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6390 =
        let uu____6391 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6391  in
      FStar_Syntax_Syntax.fvar uu____6390 FStar_Syntax_Syntax.delta_constant
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
                  let uu____6441 =
                    let uu____6446 =
                      let uu____6447 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____6447 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____6446 [u_a]
                     in
                  match uu____6441 with
                  | (uu____6458,conjunction) ->
                      let uu____6460 =
                        let uu____6469 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____6484 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____6469, uu____6484)  in
                      (match uu____6460 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____6530 =
                               let uu____6532 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____6532 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____6530)
                              in
                           let uu____6536 =
                             let uu____6581 =
                               let uu____6582 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____6582.FStar_Syntax_Syntax.n  in
                             match uu____6581 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____6631) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____6663 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____6663 with
                                  | (a_b::bs1,body1) ->
                                      let uu____6735 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____6735 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____6883 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____6883)))
                             | uu____6916 ->
                                 let uu____6917 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____6917 r
                              in
                           (match uu____6536 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____7042 =
                                  let uu____7049 =
                                    let uu____7050 =
                                      let uu____7051 =
                                        let uu____7058 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____7058, a)  in
                                      FStar_Syntax_Syntax.NT uu____7051  in
                                    [uu____7050]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____7049
                                    (fun b  ->
                                       let uu____7074 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____7076 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____7078 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____7074 uu____7076 uu____7078) r
                                   in
                                (match uu____7042 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____7116 =
                                                let uu____7123 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____7123, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____7116) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____7162 =
                                           let uu____7163 =
                                             let uu____7166 =
                                               let uu____7167 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7167.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7166
                                              in
                                           uu____7163.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7162 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7178,uu____7179::is) ->
                                             let uu____7221 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7221
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7254 ->
                                             let uu____7255 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7255 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____7271 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7271)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____7276 =
                                           let uu____7277 =
                                             let uu____7280 =
                                               let uu____7281 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____7281.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____7280
                                              in
                                           uu____7277.FStar_Syntax_Syntax.n
                                            in
                                         match uu____7276 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____7292,uu____7293::is) ->
                                             let uu____7335 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____7335
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____7368 ->
                                             let uu____7369 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____7369 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____7385 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____7385)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____7390 =
                                         let uu____7391 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____7391.FStar_Syntax_Syntax.n  in
                                       match uu____7390 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7396,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____7451 ->
                                           let uu____7452 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____7452 r
                                        in
                                     let uu____7461 =
                                       let uu____7462 =
                                         let uu____7463 =
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
                                             uu____7463;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____7462
                                        in
                                     let uu____7486 =
                                       let uu____7487 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____7487 g_guard
                                        in
                                     (uu____7461, uu____7486))))
  
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
                fun uu____7532  ->
                  let if_then_else1 =
                    let uu____7538 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____7538 FStar_Util.must  in
                  let uu____7545 = destruct_wp_comp ct1  in
                  match uu____7545 with
                  | (uu____7556,uu____7557,wp_t) ->
                      let uu____7559 = destruct_wp_comp ct2  in
                      (match uu____7559 with
                       | (uu____7570,uu____7571,wp_e) ->
                           let wp =
                             let uu____7576 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____7577 =
                               let uu____7582 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____7583 =
                                 let uu____7584 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____7593 =
                                   let uu____7604 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____7613 =
                                     let uu____7624 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____7633 =
                                       let uu____7644 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____7644]  in
                                     uu____7624 :: uu____7633  in
                                   uu____7604 :: uu____7613  in
                                 uu____7584 :: uu____7593  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____7582
                                 uu____7583
                                in
                             uu____7577 FStar_Pervasives_Native.None
                               uu____7576
                              in
                           let uu____7693 = mk_comp ed u_a a wp []  in
                           (uu____7693, FStar_TypeChecker_Env.trivial_guard))
  
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
               fun uu____7763  ->
                 match uu____7763 with
                 | (uu____7777,eff_label,uu____7779,uu____7780) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____7793 =
          let uu____7801 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____7839  ->
                    match uu____7839 with
                    | (uu____7854,uu____7855,flags,uu____7857) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_7874  ->
                                match uu___5_7874 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____7877 -> false))))
             in
          if uu____7801
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____7793 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____7914 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____7916 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____7916
              then
                let uu____7923 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____7923, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____7930 =
                       let uu____7939 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7939]  in
                     let uu____7958 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7930 uu____7958  in
                   let kwp =
                     let uu____7964 =
                       let uu____7973 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7973]  in
                     let uu____7992 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7964 uu____7992  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7999 =
                       let uu____8000 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____8000]  in
                     let uu____8019 =
                       let uu____8022 =
                         let uu____8029 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____8029
                          in
                       let uu____8030 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____8022 uu____8030  in
                     FStar_Syntax_Util.abs uu____7999 uu____8019
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
                   let uu____8054 =
                     should_not_inline_whole_match ||
                       (let uu____8057 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____8057)
                      in
                   if uu____8054 then cthen true else cthen false  in
                 let uu____8064 =
                   FStar_List.fold_right
                     (fun uu____8117  ->
                        fun uu____8118  ->
                          match (uu____8117, uu____8118) with
                          | ((g,eff_label,uu____8172,cthen),(uu____8174,celse,g_comp))
                              ->
                              let uu____8215 =
                                let uu____8220 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____8220
                                 in
                              (match uu____8215 with
                               | (cthen1,gthen) ->
                                   let uu____8231 =
                                     let uu____8240 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____8240 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____8263 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____8264 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____8263, uu____8264, g_lift)
                                      in
                                   (match uu____8231 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          let uu____8314 =
                                            FStar_All.pipe_right md
                                              FStar_Syntax_Util.is_layered
                                             in
                                          if uu____8314
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____8348 =
                                          let uu____8353 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____8353
                                           in
                                        (match uu____8348 with
                                         | (c,g_conjunction) ->
                                             let uu____8364 =
                                               let uu____8365 =
                                                 let uu____8366 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____8366 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____8365 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____8364)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____8064 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____8400::[] -> (comp, g_comp)
                      | uu____8443 ->
                          let uu____8460 =
                            let uu____8462 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            FStar_All.pipe_right uu____8462
                              FStar_Syntax_Util.is_layered
                             in
                          if uu____8460
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
                             let uu____8475 = destruct_wp_comp comp1  in
                             match uu____8475 with
                             | (uu____8486,uu____8487,wp) ->
                                 let ite_wp =
                                   let uu____8490 =
                                     FStar_All.pipe_right md1
                                       FStar_Syntax_Util.get_wp_ite_combinator
                                      in
                                   FStar_All.pipe_right uu____8490
                                     FStar_Util.must
                                    in
                                 let wp1 =
                                   let uu____8500 =
                                     let uu____8505 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_res_t] env md1 ite_wp
                                        in
                                     let uu____8506 =
                                       let uu____8507 =
                                         FStar_Syntax_Syntax.as_arg res_t  in
                                       let uu____8516 =
                                         let uu____8527 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [uu____8527]  in
                                       uu____8507 :: uu____8516  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____8505
                                       uu____8506
                                      in
                                   uu____8500 FStar_Pervasives_Native.None
                                     wp.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____8560 =
                                   mk_comp md1 u_res_t res_t wp1
                                     bind_cases_flags
                                    in
                                 (uu____8560, g_comp))))
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
          let uu____8595 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____8595 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____8611 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____8617 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____8611 uu____8617
              else
                (let uu____8626 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____8632 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____8626 uu____8632)
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
          let uu____8657 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____8657
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____8660 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____8660
        then u_res
        else
          (let is_total =
             let uu____8667 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____8667
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____8678 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____8678 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8681 =
                    let uu____8687 =
                      let uu____8689 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____8689
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____8687)
                     in
                  FStar_Errors.raise_error uu____8681
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
      let uu____8713 = destruct_wp_comp ct  in
      match uu____8713 with
      | (u_t,t,wp) ->
          let vc =
            let uu____8732 = FStar_TypeChecker_Env.get_range env  in
            let uu____8733 =
              let uu____8738 =
                let uu____8739 =
                  let uu____8740 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____8740 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____8739
                 in
              let uu____8747 =
                let uu____8748 = FStar_Syntax_Syntax.as_arg t  in
                let uu____8757 =
                  let uu____8768 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____8768]  in
                uu____8748 :: uu____8757  in
              FStar_Syntax_Syntax.mk_Tm_app uu____8738 uu____8747  in
            uu____8733 FStar_Pervasives_Native.None uu____8732  in
          let uu____8801 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____8801)
  
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
                  let uu____8856 = FStar_TypeChecker_Env.try_lookup_lid env f
                     in
                  match uu____8856 with
                  | FStar_Pervasives_Native.Some uu____8871 ->
                      ((let uu____8889 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____8889
                        then
                          let uu____8893 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____8893
                        else ());
                       (let coercion =
                          let uu____8899 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____8899
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____8906 =
                            let uu____8907 =
                              let uu____8908 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____8908
                               in
                            (FStar_Pervasives_Native.None, uu____8907)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____8906
                           in
                        let e1 =
                          let uu____8914 =
                            let uu____8919 =
                              let uu____8920 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____8920]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____8919
                             in
                          uu____8914 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8954 =
                          let uu____8960 =
                            let uu____8962 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____8962
                             in
                          (FStar_Errors.Warning_CoercionNotFound, uu____8960)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____8954);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____8981 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____8999 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____9010 -> false 
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
      let uu____9034 = FStar_Syntax_Util.head_and_args t2  in
      match uu____9034 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____9079 =
              let uu____9094 =
                let uu____9095 = FStar_Syntax_Subst.compress h1  in
                uu____9095.FStar_Syntax_Syntax.n  in
              (uu____9094, args)  in
            match uu____9079 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____9142,uu____9143) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____9176) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match (uu____9197,branches),uu____9199)
                ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____9263 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____9264 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____9264 with
                               | (uu____9265,uu____9266,br_body) ->
                                   let uu____9284 =
                                     let uu____9285 =
                                       let uu____9290 =
                                         let uu____9291 =
                                           let uu____9294 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____9294
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____9291
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____9290  in
                                     FStar_All.pipe_right br_body uu____9285
                                      in
                                   (match uu____9284 with
                                    | No  -> No
                                    | uu____9305 -> Maybe))) No)
            | uu____9306 -> No  in
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
            (((let uu____9358 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____9358) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9377 =
                 let uu____9378 = FStar_Syntax_Subst.compress t1  in
                 uu____9378.FStar_Syntax_Syntax.n  in
               match uu____9377 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____9383 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9393 =
                 let uu____9394 = FStar_Syntax_Subst.compress t1  in
                 uu____9394.FStar_Syntax_Syntax.n  in
               match uu____9393 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____9399 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____9409 =
                 let uu____9410 = FStar_Syntax_Subst.compress t1  in
                 uu____9410.FStar_Syntax_Syntax.n  in
               match uu____9409 with
               | FStar_Syntax_Syntax.Tm_type uu____9414 -> true
               | uu____9416 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____9419 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____9419 with
             | (head1,args) ->
                 ((let uu____9469 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____9469
                   then
                     let uu____9473 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____9475 = FStar_Syntax_Print.term_to_string e  in
                     let uu____9477 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____9479 = FStar_Syntax_Print.term_to_string exp_t
                        in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____9473 uu____9475 uu____9477 uu____9479
                   else ());
                  (let mk_erased u t =
                     let uu____9497 =
                       let uu____9500 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____9500 [u]  in
                     let uu____9501 =
                       let uu____9512 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____9512]  in
                     FStar_Syntax_Util.mk_app uu____9497 uu____9501  in
                   let uu____9537 =
                     let uu____9552 =
                       let uu____9553 = FStar_Syntax_Util.un_uinst head1  in
                       uu____9553.FStar_Syntax_Syntax.n  in
                     (uu____9552, args)  in
                   match uu____9537 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____9591 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____9591 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____9631 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____9631 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____9671 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____9671 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____9711 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____9711 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____9732 ->
                       let uu____9747 =
                         let uu____9752 = check_erased env res_typ  in
                         let uu____9753 = check_erased env exp_t  in
                         (uu____9752, uu____9753)  in
                       (match uu____9747 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____9762 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____9762 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____9773 =
                                   let uu____9778 =
                                     let uu____9779 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____9779]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____9778
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____9773 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____9814 =
                              let uu____9819 =
                                let uu____9820 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____9820]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____9819
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____9814 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____9853 ->
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
        let uu____9888 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____9888 with
        | (hd1,args) ->
            let uu____9937 =
              let uu____9952 =
                let uu____9953 = FStar_Syntax_Subst.compress hd1  in
                uu____9953.FStar_Syntax_Syntax.n  in
              (uu____9952, args)  in
            (match uu____9937 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____9991 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _10018  -> FStar_Pervasives_Native.Some _10018)
                   uu____9991
             | uu____10019 -> FStar_Pervasives_Native.None)
  
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
          (let uu____10072 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____10072
           then
             let uu____10075 = FStar_Syntax_Print.term_to_string e  in
             let uu____10077 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____10079 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____10075 uu____10077 uu____10079
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____10089 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____10089 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____10114 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____10140 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____10140, false)
             else
               (let uu____10150 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____10150, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____10163) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____10175 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____10175
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1233_10191 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1233_10191.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1233_10191.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1233_10191.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____10198 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____10198 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____10214 =
                      let uu____10215 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____10215 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____10235 =
                            let uu____10237 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____10237 = FStar_Syntax_Util.Equal  in
                          if uu____10235
                          then
                            ((let uu____10244 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____10244
                              then
                                let uu____10248 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____10250 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____10248 uu____10250
                              else ());
                             (let uu____10255 = set_result_typ1 c  in
                              (uu____10255, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____10262 ->
                                   true
                               | uu____10270 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____10279 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____10279
                                  in
                               let lc1 =
                                 let uu____10281 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____10282 =
                                   let uu____10283 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____10283)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____10281 uu____10282
                                  in
                               ((let uu____10287 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10287
                                 then
                                   let uu____10291 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____10293 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____10295 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____10297 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____10291 uu____10293 uu____10295
                                     uu____10297
                                 else ());
                                (let uu____10302 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____10302 with
                                 | (c1,g_lc) ->
                                     let uu____10313 = set_result_typ1 c1  in
                                     let uu____10314 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____10313, uu____10314)))
                             else
                               ((let uu____10318 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____10318
                                 then
                                   let uu____10322 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____10324 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____10322 uu____10324
                                 else ());
                                (let uu____10329 = set_result_typ1 c  in
                                 (uu____10329, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1270_10333 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1270_10333.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1270_10333.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1270_10333.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____10343 =
                      let uu____10344 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____10344
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____10354 =
                           let uu____10355 = FStar_Syntax_Subst.compress f1
                              in
                           uu____10355.FStar_Syntax_Syntax.n  in
                         match uu____10354 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____10362,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____10364;
                                            FStar_Syntax_Syntax.vars =
                                              uu____10365;_},uu____10366)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1286_10392 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1286_10392.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1286_10392.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1286_10392.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____10393 ->
                             let uu____10394 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____10394 with
                              | (c,g_c) ->
                                  ((let uu____10406 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____10406
                                    then
                                      let uu____10410 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____10412 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____10414 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____10416 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____10410 uu____10412 uu____10414
                                        uu____10416
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
                                        let uu____10429 =
                                          let uu____10434 =
                                            let uu____10435 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____10435]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____10434
                                           in
                                        uu____10429
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____10462 =
                                      let uu____10467 =
                                        FStar_All.pipe_left
                                          (fun _10488  ->
                                             FStar_Pervasives_Native.Some
                                               _10488)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____10489 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____10490 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____10491 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____10467
                                        uu____10489 e uu____10490 uu____10491
                                       in
                                    match uu____10462 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1304_10499 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1304_10499.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1304_10499.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____10501 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____10501
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____10504 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____10504 with
                                         | (c2,g_lc) ->
                                             ((let uu____10516 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____10516
                                               then
                                                 let uu____10520 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____10520
                                               else ());
                                              (let uu____10525 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____10525))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_10534  ->
                              match uu___6_10534 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____10537 -> []))
                       in
                    let lc1 =
                      let uu____10539 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____10539 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1320_10541 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1320_10541.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1320_10541.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1320_10541.FStar_TypeChecker_Common.implicits)
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
        let uu____10577 =
          let uu____10580 =
            let uu____10585 =
              let uu____10586 =
                let uu____10595 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____10595  in
              [uu____10586]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____10585  in
          uu____10580 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____10577  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____10618 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____10618
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____10637 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____10653 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____10670 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____10670
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____10686)::(ens,uu____10688)::uu____10689 ->
                    let uu____10732 =
                      let uu____10735 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____10735  in
                    let uu____10736 =
                      let uu____10737 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____10737  in
                    (uu____10732, uu____10736)
                | uu____10740 ->
                    let uu____10751 =
                      let uu____10757 =
                        let uu____10759 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____10759
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____10757)
                       in
                    FStar_Errors.raise_error uu____10751
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____10779)::uu____10780 ->
                    let uu____10807 =
                      let uu____10812 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____10812
                       in
                    (match uu____10807 with
                     | (us_r,uu____10844) ->
                         let uu____10845 =
                           let uu____10850 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____10850
                            in
                         (match uu____10845 with
                          | (us_e,uu____10882) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____10885 =
                                  let uu____10886 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10886
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10885
                                  us_r
                                 in
                              let as_ens =
                                let uu____10888 =
                                  let uu____10889 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____10889
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____10888
                                  us_e
                                 in
                              let req =
                                let uu____10893 =
                                  let uu____10898 =
                                    let uu____10899 =
                                      let uu____10910 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10910]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10899
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____10898
                                   in
                                uu____10893 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____10950 =
                                  let uu____10955 =
                                    let uu____10956 =
                                      let uu____10967 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10967]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____10956
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____10955
                                   in
                                uu____10950 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____11004 =
                                let uu____11007 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____11007  in
                              let uu____11008 =
                                let uu____11009 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____11009  in
                              (uu____11004, uu____11008)))
                | uu____11012 -> failwith "Impossible"))
  
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
        (let uu____11051 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____11051
         then
           let uu____11056 = FStar_Syntax_Print.term_to_string tm  in
           let uu____11058 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____11056
             uu____11058
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
          (let uu____11117 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____11117
           then
             let uu____11122 = FStar_Syntax_Print.term_to_string tm  in
             let uu____11124 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____11122
               uu____11124
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____11135 =
      let uu____11137 =
        let uu____11138 = FStar_Syntax_Subst.compress t  in
        uu____11138.FStar_Syntax_Syntax.n  in
      match uu____11137 with
      | FStar_Syntax_Syntax.Tm_app uu____11142 -> false
      | uu____11160 -> true  in
    if uu____11135
    then t
    else
      (let uu____11165 = FStar_Syntax_Util.head_and_args t  in
       match uu____11165 with
       | (head1,args) ->
           let uu____11208 =
             let uu____11210 =
               let uu____11211 = FStar_Syntax_Subst.compress head1  in
               uu____11211.FStar_Syntax_Syntax.n  in
             match uu____11210 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____11216 -> false  in
           if uu____11208
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____11248 ->
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
          ((let uu____11295 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____11295
            then
              let uu____11298 = FStar_Syntax_Print.term_to_string e  in
              let uu____11300 = FStar_Syntax_Print.term_to_string t  in
              let uu____11302 =
                let uu____11304 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____11304
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____11298 uu____11300 uu____11302
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____11317 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____11317 with
              | (formals,uu____11333) ->
                  let n_implicits =
                    let uu____11355 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____11433  ->
                              match uu____11433 with
                              | (uu____11441,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____11448 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____11448 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____11355 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____11573 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____11573 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____11587 =
                      let uu____11593 =
                        let uu____11595 = FStar_Util.string_of_int n_expected
                           in
                        let uu____11597 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____11599 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____11595 uu____11597 uu____11599
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____11593)
                       in
                    let uu____11603 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____11587 uu____11603
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_11621 =
              match uu___7_11621 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____11664 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____11664 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _11795,uu____11782)
                           when _11795 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____11828,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____11830))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____11864 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____11864 with
                            | (v1,uu____11905,g) ->
                                ((let uu____11920 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____11920
                                  then
                                    let uu____11923 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____11923
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____11933 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____11933 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____12026 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____12026))))
                       | (uu____12053,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____12090 =
                             let uu____12103 =
                               let uu____12110 =
                                 let uu____12115 = FStar_Dyn.mkdyn env  in
                                 (uu____12115, tau)  in
                               FStar_Pervasives_Native.Some uu____12110  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____12103
                              in
                           (match uu____12090 with
                            | (v1,uu____12148,g) ->
                                ((let uu____12163 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____12163
                                  then
                                    let uu____12166 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____12166
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____12176 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____12176 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____12269 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____12269))))
                       | (uu____12296,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____12344 =
                       let uu____12371 = inst_n_binders t1  in
                       aux [] uu____12371 bs1  in
                     (match uu____12344 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____12443) -> (e, torig, guard)
                           | (uu____12474,[]) when
                               let uu____12505 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____12505 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____12507 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____12535 ->
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
            | uu____12548 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____12560 =
      let uu____12564 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____12564
        (FStar_List.map
           (fun u  ->
              let uu____12576 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____12576 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____12560 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____12604 = FStar_Util.set_is_empty x  in
      if uu____12604
      then []
      else
        (let s =
           let uu____12622 =
             let uu____12625 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____12625  in
           FStar_All.pipe_right uu____12622 FStar_Util.set_elements  in
         (let uu____12641 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____12641
          then
            let uu____12646 =
              let uu____12648 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____12648  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____12646
          else ());
         (let r =
            let uu____12657 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____12657  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____12696 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____12696
                     then
                       let uu____12701 =
                         let uu____12703 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____12703
                          in
                       let uu____12707 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____12709 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____12701 uu____12707 uu____12709
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
        let uu____12739 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____12739 FStar_Util.set_elements  in
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
        | ([],uu____12778) -> generalized_univ_names
        | (uu____12785,[]) -> explicit_univ_names
        | uu____12792 ->
            let uu____12801 =
              let uu____12807 =
                let uu____12809 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____12809
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____12807)
               in
            FStar_Errors.raise_error uu____12801 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____12831 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____12831
       then
         let uu____12836 = FStar_Syntax_Print.term_to_string t  in
         let uu____12838 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____12836 uu____12838
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____12847 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____12847
        then
          let uu____12852 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____12852
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____12861 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____12861
         then
           let uu____12866 = FStar_Syntax_Print.term_to_string t  in
           let uu____12868 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____12866 uu____12868
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
        let uu____12952 =
          let uu____12954 =
            FStar_Util.for_all
              (fun uu____12968  ->
                 match uu____12968 with
                 | (uu____12978,uu____12979,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____12954  in
        if uu____12952
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____13031 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____13031
              then
                let uu____13034 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____13034
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____13041 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____13041
               then
                 let uu____13044 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____13044
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____13062 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____13062 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____13096 =
             match uu____13096 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____13133 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____13133
                   then
                     let uu____13138 =
                       let uu____13140 =
                         let uu____13144 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____13144
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____13140
                         (FStar_String.concat ", ")
                        in
                     let uu____13192 =
                       let uu____13194 =
                         let uu____13198 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____13198
                           (FStar_List.map
                              (fun u  ->
                                 let uu____13211 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____13213 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____13211
                                   uu____13213))
                          in
                       FStar_All.pipe_right uu____13194
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____13138
                       uu____13192
                   else ());
                  (let univs2 =
                     let uu____13227 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____13239 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____13239) univs1
                       uu____13227
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____13246 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____13246
                    then
                      let uu____13251 =
                        let uu____13253 =
                          let uu____13257 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____13257
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____13253
                          (FStar_String.concat ", ")
                         in
                      let uu____13305 =
                        let uu____13307 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____13321 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____13323 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____13321
                                    uu____13323))
                           in
                        FStar_All.pipe_right uu____13307
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____13251 uu____13305
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____13344 =
             let uu____13361 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____13361  in
           match uu____13344 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____13451 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____13451
                 then ()
                 else
                   (let uu____13456 = lec_hd  in
                    match uu____13456 with
                    | (lb1,uu____13464,uu____13465) ->
                        let uu____13466 = lec2  in
                        (match uu____13466 with
                         | (lb2,uu____13474,uu____13475) ->
                             let msg =
                               let uu____13478 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____13480 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____13478 uu____13480
                                in
                             let uu____13483 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____13483))
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
                 let uu____13551 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____13551
                 then ()
                 else
                   (let uu____13556 = lec_hd  in
                    match uu____13556 with
                    | (lb1,uu____13564,uu____13565) ->
                        let uu____13566 = lec2  in
                        (match uu____13566 with
                         | (lb2,uu____13574,uu____13575) ->
                             let msg =
                               let uu____13578 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____13580 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____13578 uu____13580
                                in
                             let uu____13583 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____13583))
                  in
               let lecs1 =
                 let uu____13594 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____13647 = univs_and_uvars_of_lec this_lec  in
                        match uu____13647 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____13594 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____13752 = lec_hd  in
                   match uu____13752 with
                   | (lbname,e,c) ->
                       let uu____13762 =
                         let uu____13768 =
                           let uu____13770 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____13772 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____13774 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____13770 uu____13772 uu____13774
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____13768)
                          in
                       let uu____13778 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____13762 uu____13778
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____13797 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____13797 with
                         | FStar_Pervasives_Native.Some uu____13806 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____13814 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____13818 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____13818 with
                              | (bs,kres) ->
                                  ((let uu____13862 =
                                      let uu____13863 =
                                        let uu____13866 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____13866
                                         in
                                      uu____13863.FStar_Syntax_Syntax.n  in
                                    match uu____13862 with
                                    | FStar_Syntax_Syntax.Tm_type uu____13867
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____13871 =
                                          let uu____13873 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____13873  in
                                        if uu____13871
                                        then fail1 kres
                                        else ()
                                    | uu____13878 -> fail1 kres);
                                   (let a =
                                      let uu____13880 =
                                        let uu____13883 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _13886  ->
                                             FStar_Pervasives_Native.Some
                                               _13886) uu____13883
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____13880
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____13894 ->
                                          let uu____13903 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____13903
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
                      (fun uu____14006  ->
                         match uu____14006 with
                         | (lbname,e,c) ->
                             let uu____14052 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____14113 ->
                                   let uu____14126 = (e, c)  in
                                   (match uu____14126 with
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
                                                (fun uu____14166  ->
                                                   match uu____14166 with
                                                   | (x,uu____14172) ->
                                                       let uu____14173 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____14173)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____14191 =
                                                let uu____14193 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____14193
                                                 in
                                              if uu____14191
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
                                          let uu____14202 =
                                            let uu____14203 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____14203.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14202 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____14228 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____14228 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____14239 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____14243 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____14243, gen_tvars))
                                in
                             (match uu____14052 with
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
        (let uu____14390 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____14390
         then
           let uu____14393 =
             let uu____14395 =
               FStar_List.map
                 (fun uu____14410  ->
                    match uu____14410 with
                    | (lb,uu____14419,uu____14420) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____14395 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____14393
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____14446  ->
                match uu____14446 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____14475 = gen env is_rec lecs  in
           match uu____14475 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____14574  ->
                       match uu____14574 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____14636 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____14636
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____14684  ->
                           match uu____14684 with
                           | (l,us,e,c,gvs) ->
                               let uu____14718 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____14720 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____14722 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____14724 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____14726 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____14718 uu____14720 uu____14722
                                 uu____14724 uu____14726))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____14771  ->
                match uu____14771 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____14815 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____14815, t, c, gvs)) univnames_lecs
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
        let uu____14870 =
          let uu____14874 =
            let uu____14876 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____14876  in
          FStar_Pervasives_Native.Some uu____14874  in
        FStar_Profiling.profile
          (fun uu____14893  -> generalize' env is_rec lecs) uu____14870
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
              (let uu____14953 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____14953 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____14959 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _14962  -> FStar_Pervasives_Native.Some _14962)
                     uu____14959)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1777_14982 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1777_14982.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1777_14982.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____14983 -> e2  in
          let uu____14984 = maybe_coerce_lc env1 e lc t2  in
          match uu____14984 with
          | (e1,lc1,g_c) ->
              let uu____15000 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____15000 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15009 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____15015 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____15009 uu____15015
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____15024 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____15024
                     then
                       let uu____15029 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____15029
                     else ());
                    (let uu____15035 = decorate e1 t2  in
                     let uu____15036 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (uu____15035, lc1, uu____15036))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____15064 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____15064
         then
           let uu____15067 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____15067
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____15081 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____15081 with
         | (c,g_c) ->
             let uu____15093 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____15093
             then
               let uu____15101 =
                 let uu____15103 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____15103  in
               (uu____15101, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____15111 =
                    let uu____15112 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____15112
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____15111
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____15113 = check_trivial_precondition env c1  in
                match uu____15113 with
                | (ct,vc,g_pre) ->
                    ((let uu____15129 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____15129
                      then
                        let uu____15134 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____15134
                      else ());
                     (let uu____15139 =
                        let uu____15141 =
                          let uu____15142 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____15142  in
                        discharge uu____15141  in
                      let uu____15143 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____15139, uu____15143)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_15177 =
        match uu___8_15177 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____15187)::[] -> f fst1
        | uu____15212 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____15224 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____15224
          (fun _15225  -> FStar_TypeChecker_Common.NonTrivial _15225)
         in
      let op_or_e e =
        let uu____15236 =
          let uu____15237 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____15237  in
        FStar_All.pipe_right uu____15236
          (fun _15240  -> FStar_TypeChecker_Common.NonTrivial _15240)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _15247  -> FStar_TypeChecker_Common.NonTrivial _15247)
         in
      let op_or_t t =
        let uu____15258 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____15258
          (fun _15261  -> FStar_TypeChecker_Common.NonTrivial _15261)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _15268  -> FStar_TypeChecker_Common.NonTrivial _15268)
         in
      let short_op_ite uu___9_15274 =
        match uu___9_15274 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____15284)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____15311)::[] ->
            let uu____15352 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____15352
              (fun _15353  -> FStar_TypeChecker_Common.NonTrivial _15353)
        | uu____15354 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____15366 =
          let uu____15374 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____15374)  in
        let uu____15382 =
          let uu____15392 =
            let uu____15400 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____15400)  in
          let uu____15408 =
            let uu____15418 =
              let uu____15426 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____15426)  in
            let uu____15434 =
              let uu____15444 =
                let uu____15452 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____15452)  in
              let uu____15460 =
                let uu____15470 =
                  let uu____15478 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____15478)  in
                [uu____15470; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____15444 :: uu____15460  in
            uu____15418 :: uu____15434  in
          uu____15392 :: uu____15408  in
        uu____15366 :: uu____15382  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____15540 =
            FStar_Util.find_map table
              (fun uu____15555  ->
                 match uu____15555 with
                 | (x,mk1) ->
                     let uu____15572 = FStar_Ident.lid_equals x lid  in
                     if uu____15572
                     then
                       let uu____15577 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____15577
                     else FStar_Pervasives_Native.None)
             in
          (match uu____15540 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____15581 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____15589 =
      let uu____15590 = FStar_Syntax_Util.un_uinst l  in
      uu____15590.FStar_Syntax_Syntax.n  in
    match uu____15589 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____15595 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____15631)::uu____15632 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____15651 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____15660,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____15661))::uu____15662 -> bs
      | uu____15680 ->
          let uu____15681 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____15681 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____15685 =
                 let uu____15686 = FStar_Syntax_Subst.compress t  in
                 uu____15686.FStar_Syntax_Syntax.n  in
               (match uu____15685 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____15690) ->
                    let uu____15711 =
                      FStar_Util.prefix_until
                        (fun uu___10_15751  ->
                           match uu___10_15751 with
                           | (uu____15759,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____15760)) ->
                               false
                           | uu____15765 -> true) bs'
                       in
                    (match uu____15711 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____15801,uu____15802) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____15874,uu____15875) ->
                         let uu____15948 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____15968  ->
                                   match uu____15968 with
                                   | (x,uu____15977) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____15948
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____16026  ->
                                     match uu____16026 with
                                     | (x,i) ->
                                         let uu____16045 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____16045, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____16056 -> bs))
  
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
            let uu____16085 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____16085
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
          let uu____16116 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____16116
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
        (let uu____16159 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____16159
         then
           ((let uu____16164 = FStar_Ident.text_of_lid lident  in
             d uu____16164);
            (let uu____16166 = FStar_Ident.text_of_lid lident  in
             let uu____16168 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____16166 uu____16168))
         else ());
        (let fv =
           let uu____16174 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____16174
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
         let uu____16186 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___1938_16188 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1938_16188.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1938_16188.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1938_16188.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1938_16188.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___1938_16188.FStar_Syntax_Syntax.sigopts)
           }), uu____16186))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_16206 =
        match uu___11_16206 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16209 -> false  in
      let reducibility uu___12_16217 =
        match uu___12_16217 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____16224 -> false  in
      let assumption uu___13_16232 =
        match uu___13_16232 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____16236 -> false  in
      let reification uu___14_16244 =
        match uu___14_16244 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____16247 -> true
        | uu____16249 -> false  in
      let inferred uu___15_16257 =
        match uu___15_16257 with
        | FStar_Syntax_Syntax.Discriminator uu____16259 -> true
        | FStar_Syntax_Syntax.Projector uu____16261 -> true
        | FStar_Syntax_Syntax.RecordType uu____16267 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____16277 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____16290 -> false  in
      let has_eq uu___16_16298 =
        match uu___16_16298 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____16302 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____16381 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____16388 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____16421 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____16421))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____16452 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____16452
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
           | FStar_Syntax_Syntax.Sig_bundle uu____16472 ->
               let uu____16481 =
                 let uu____16483 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_16489  ->
                           match uu___17_16489 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____16492 -> false))
                    in
                 Prims.op_Negation uu____16483  in
               if uu____16481
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____16499 -> ()
           | uu____16506 ->
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
      let uu____16520 =
        let uu____16522 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_16528  ->
                  match uu___18_16528 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____16531 -> false))
           in
        FStar_All.pipe_right uu____16522 Prims.op_Negation  in
      if uu____16520
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____16552 =
            let uu____16558 =
              let uu____16560 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____16560 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____16558)  in
          FStar_Errors.raise_error uu____16552 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____16578 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____16586 =
            let uu____16588 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____16588  in
          if uu____16586 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____16599),uu____16600) ->
              ((let uu____16612 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____16612
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____16621 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____16621
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____16632 ->
              ((let uu____16642 =
                  let uu____16644 =
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
                  Prims.op_Negation uu____16644  in
                if uu____16642 then err'1 () else ());
               (let uu____16654 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_16660  ->
                           match uu___19_16660 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____16663 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____16654
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____16669 ->
              let uu____16676 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____16676 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____16684 ->
              let uu____16691 =
                let uu____16693 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____16693  in
              if uu____16691 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____16703 ->
              let uu____16704 =
                let uu____16706 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____16706  in
              if uu____16704 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16716 ->
              let uu____16729 =
                let uu____16731 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____16731  in
              if uu____16729 then err'1 () else ()
          | uu____16741 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____16780 =
          let uu____16781 = FStar_Syntax_Subst.compress t1  in
          uu____16781.FStar_Syntax_Syntax.n  in
        match uu____16780 with
        | FStar_Syntax_Syntax.Tm_arrow uu____16785 ->
            let uu____16800 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____16800 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____16833;
               FStar_Syntax_Syntax.index = uu____16834;
               FStar_Syntax_Syntax.sort = t2;_},uu____16836)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____16845) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____16871) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____16877 -> false
      
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
        (let uu____16887 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____16887
         then
           let uu____16892 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____16892
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
                  let uu____16957 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____16957 r  in
                let uu____16967 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____16967 with
                | (uu____16976,signature) ->
                    let uu____16978 =
                      let uu____16979 = FStar_Syntax_Subst.compress signature
                         in
                      uu____16979.FStar_Syntax_Syntax.n  in
                    (match uu____16978 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16987) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____17035 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____17050 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____17052 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____17050 eff_name.FStar_Ident.str
                                       uu____17052) r
                                 in
                              (match uu____17035 with
                               | (is,g) ->
                                   let uu____17065 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____17067 =
                                             let uu____17068 =
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
                                                 = uu____17068;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____17067
                                            in
                                         let uu____17087 =
                                           let uu____17094 =
                                             let uu____17095 =
                                               let uu____17110 =
                                                 let uu____17119 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____17119]  in
                                               (uu____17110, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____17095
                                              in
                                           FStar_Syntax_Syntax.mk uu____17094
                                            in
                                         uu____17087
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____17150 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____17150
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____17159 =
                                           let uu____17164 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____17164
                                            in
                                         uu____17159
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____17065, g))
                          | uu____17173 -> fail1 signature)
                     | uu____17174 -> fail1 signature)
  
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
            let uu____17205 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____17205
              (fun ed  ->
                 let uu____17213 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____17213 u a_tm)
  
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
              let uu____17249 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____17249 with
              | (uu____17254,sig_tm) ->
                  let fail1 t =
                    let uu____17262 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____17262 r  in
                  let uu____17268 =
                    let uu____17269 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____17269.FStar_Syntax_Syntax.n  in
                  (match uu____17268 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____17273) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____17296)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____17318 -> fail1 sig_tm)
                   | uu____17319 -> fail1 sig_tm)
  
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
          (let uu____17350 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____17350
           then
             let uu____17355 = FStar_Syntax_Print.comp_to_string c  in
             let uu____17357 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____17355 uu____17357
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____17364 =
             let uu____17375 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____17376 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____17375, (ct.FStar_Syntax_Syntax.result_typ), uu____17376)
              in
           match uu____17364 with
           | (u,a,c_is) ->
               let uu____17424 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____17424 with
                | (uu____17433,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____17444 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____17446 = FStar_Ident.string_of_lid tgt  in
                      let uu____17448 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____17444 uu____17446 s uu____17448
                       in
                    let uu____17451 =
                      let uu____17484 =
                        let uu____17485 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____17485.FStar_Syntax_Syntax.n  in
                      match uu____17484 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____17549 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____17549 with
                           | (a_b::bs1,c2) ->
                               let uu____17609 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____17671 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____17609, uu____17671))
                      | uu____17698 ->
                          let uu____17699 =
                            let uu____17705 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____17705)
                             in
                          FStar_Errors.raise_error uu____17699 r
                       in
                    (match uu____17451 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____17823 =
                           let uu____17830 =
                             let uu____17831 =
                               let uu____17832 =
                                 let uu____17839 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____17839, a)  in
                               FStar_Syntax_Syntax.NT uu____17832  in
                             [uu____17831]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____17830
                             (fun b  ->
                                let uu____17856 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____17858 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____17860 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____17862 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____17856 uu____17858 uu____17860
                                  uu____17862) r
                            in
                         (match uu____17823 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____17876 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____17876
                                then
                                  let uu____17881 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____17890 =
                                             let uu____17892 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____17892
                                              in
                                           Prims.op_Hat s uu____17890) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____17881
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____17923 =
                                           let uu____17930 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____17930, t)  in
                                         FStar_Syntax_Syntax.NT uu____17923)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____17949 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____17949
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____17955 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____17955
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____17964 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____17964)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____17968 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____17968 r
                                   in
                                let c1 =
                                  let uu____17971 =
                                    let uu____17972 =
                                      let uu____17983 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____17983
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____17972;
                                      FStar_Syntax_Syntax.flags = []
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____17971  in
                                (let uu____18003 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____18003
                                 then
                                   let uu____18008 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____18008
                                 else ());
                                (let uu____18013 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____18013))))))))
  
let lift_tf_layered_effect_term :
  'Auu____18027 .
    'Auu____18027 ->
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
              let uu____18056 =
                let uu____18061 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____18061
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____18056 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____18104 =
                let uu____18105 =
                  let uu____18108 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____18108
                    FStar_Syntax_Subst.compress
                   in
                uu____18105.FStar_Syntax_Syntax.n  in
              match uu____18104 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____18131::bs,uu____18133)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____18173 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____18173
                    FStar_Pervasives_Native.fst
              | uu____18279 ->
                  let uu____18280 =
                    let uu____18286 =
                      let uu____18288 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____18288
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____18286)  in
                  FStar_Errors.raise_error uu____18280
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____18315 = FStar_Syntax_Syntax.as_arg a  in
              let uu____18324 =
                let uu____18335 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____18371  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____18378 =
                  let uu____18389 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____18389]  in
                FStar_List.append uu____18335 uu____18378  in
              uu____18315 :: uu____18324  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____18460 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____18460 with
        | (uu____18465,t) ->
            let err n1 =
              let uu____18475 =
                let uu____18481 =
                  let uu____18483 = FStar_Ident.string_of_lid datacon  in
                  let uu____18485 = FStar_Util.string_of_int n1  in
                  let uu____18487 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____18483 uu____18485 uu____18487
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____18481)
                 in
              let uu____18491 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____18475 uu____18491  in
            let uu____18492 =
              let uu____18493 = FStar_Syntax_Subst.compress t  in
              uu____18493.FStar_Syntax_Syntax.n  in
            (match uu____18492 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18497) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____18552  ->
                           match uu____18552 with
                           | (uu____18560,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____18569 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____18601 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____18601
                      FStar_Pervasives_Native.fst)
             | uu____18612 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____18625 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____18625
      then
        let uu____18628 =
          let uu____18641 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____18641
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____18628;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18676 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____18676 with
           | (uu____18685,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____18704 =
                 let uu____18705 =
                   let uu___2305_18706 = ct  in
                   let uu____18707 =
                     let uu____18718 =
                       let uu____18727 =
                         let uu____18728 =
                           let uu____18735 =
                             let uu____18736 =
                               let uu____18753 =
                                 let uu____18764 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____18764; wp]  in
                               (lift_t, uu____18753)  in
                             FStar_Syntax_Syntax.Tm_app uu____18736  in
                           FStar_Syntax_Syntax.mk uu____18735  in
                         uu____18728 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____18727
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____18718]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2305_18706.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2305_18706.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____18707;
                     FStar_Syntax_Syntax.flags =
                       (uu___2305_18706.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____18705  in
               (uu____18704, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____18864 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____18864 with
           | (uu____18871,lift_t) ->
               let uu____18873 =
                 let uu____18880 =
                   let uu____18881 =
                     let uu____18898 =
                       let uu____18909 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____18918 =
                         let uu____18929 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____18938 =
                           let uu____18949 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____18949]  in
                         uu____18929 :: uu____18938  in
                       uu____18909 :: uu____18918  in
                     (lift_t, uu____18898)  in
                   FStar_Syntax_Syntax.Tm_app uu____18881  in
                 FStar_Syntax_Syntax.mk uu____18880  in
               uu____18873 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____19002 =
           let uu____19015 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____19015 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____19002;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____19051  ->
                        fun uu____19052  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____19075 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____19075
  
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
  