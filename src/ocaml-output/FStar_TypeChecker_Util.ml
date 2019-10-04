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
<<<<<<< HEAD
    fun xs  ->
      fun g  ->
        let uu____84 =
          let uu____86 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____86  in
        if uu____84
        then g
        else
          (let uu____93 =
             FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
               (FStar_List.partition
                  (fun uu____145  ->
                     match uu____145 with
                     | (uu____152,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____93 with
           | (solve_now,defer) ->
               ((let uu____187 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____187
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____204  ->
                         match uu____204 with
                         | (s,p) ->
                             let uu____214 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____214)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____229  ->
                         match uu____229 with
                         | (s,p) ->
                             let uu____239 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____239) defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___48_247 = g  in
                      {
<<<<<<< HEAD
                        FStar_TypeChecker_Common.guard_f =
                          (uu___46_247.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred = solve_now;
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___46_247.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___46_247.FStar_TypeChecker_Common.implicits)
=======
                        FStar_TypeChecker_Env.guard_f =
                          (uu___48_247.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___48_247.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
<<<<<<< HEAD
                          (uu___47_247.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                          (uu___48_247.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
                      })
                    in
                 let g2 =
                   let uu___51_249 = g1  in
                   {
<<<<<<< HEAD
                     FStar_TypeChecker_Common.guard_f =
                       (uu___49_249.FStar_TypeChecker_Common.guard_f);
                     FStar_TypeChecker_Common.deferred = defer;
                     FStar_TypeChecker_Common.univ_ineqs =
                       (uu___49_249.FStar_TypeChecker_Common.univ_ineqs);
                     FStar_TypeChecker_Common.implicits =
                       (uu___49_249.FStar_TypeChecker_Common.implicits)
=======
                     FStar_TypeChecker_Env.guard_f =
                       (uu___51_249.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___51_249.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
<<<<<<< HEAD
                       (uu___50_249.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                       (uu___51_249.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
                   }  in
                 g2)))
=======
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
                      (let uu___48_248 = g  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___48_248.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred = solve_now;
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___48_248.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits =
                           (uu___48_248.FStar_TypeChecker_Common.implicits)
                       })
                     in
                  let g2 =
                    let uu___51_250 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___51_250.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred = defer;
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___51_250.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits =
                        (uu___51_250.FStar_TypeChecker_Common.implicits)
                    }  in
                  g2))
          else g
>>>>>>> snap
  
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
<<<<<<< HEAD
            (let uu___166_1077 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___166_1077.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___166_1077.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___166_1077.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___166_1077.FStar_Syntax_Syntax.effect_args);
=======
            (let uu___168_1080 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___168_1080.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___168_1080.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___168_1080.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___168_1080.FStar_Syntax_Syntax.effect_args);
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
            let uu___243_1577 = g  in
            let uu____1578 =
              let uu____1579 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1579  in
=======
            let uu___245_1580 = g  in
            let uu____1581 =
              let uu____1582 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1582  in
>>>>>>> snap
            {
              FStar_TypeChecker_Common.guard_f = uu____1581;
              FStar_TypeChecker_Common.deferred =
<<<<<<< HEAD
                (uu___243_1577.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___243_1577.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___243_1577.FStar_TypeChecker_Common.implicits)
=======
            let uu___241_1627 = g  in
=======
            let uu___242_1627 = g  in
>>>>>>> snap
            let uu____1628 =
              let uu____1629 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____1629  in
            {
              FStar_TypeChecker_Env.guard_f = uu____1628;
              FStar_TypeChecker_Env.deferred =
                (uu___242_1627.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___242_1627.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
<<<<<<< HEAD
                (uu___241_1627.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                (uu___242_1627.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                (uu___245_1580.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___245_1580.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___245_1580.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
               (uu____4773,
                 (let uu___588_4776 = g0  in
=======
               (uu____2830,
<<<<<<< HEAD
                 (let uu___414_2833 = g0  in
>>>>>>> snap
=======
                 (let uu___415_2833 = g0  in
>>>>>>> snap
=======
               (uu____4740,
                 (let uu___578_4743 = g0  in
>>>>>>> single tentative commit which could be reverted later
=======
               (uu____4745,
                 (let uu___579_4748 = g0  in
>>>>>>> snap
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
<<<<<<< HEAD
                    FStar_TypeChecker_Common.deferred =
<<<<<<< HEAD
<<<<<<< HEAD
                      (uu___588_4776.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___588_4776.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___588_4776.FStar_TypeChecker_Common.implicits)
=======
                    FStar_TypeChecker_Env.deferred =
                      (uu___415_2833.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___415_2833.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
<<<<<<< HEAD
                      (uu___414_2833.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                      (uu___415_2833.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                      (uu___578_4743.FStar_TypeChecker_Common.deferred);
=======
                      (uu___579_4748.FStar_TypeChecker_Common.deferred);
>>>>>>> snap
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___579_4748.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
<<<<<<< HEAD
                      (uu___578_4743.FStar_TypeChecker_Common.implicits)
>>>>>>> single tentative commit which could be reverted later
=======
                      (uu___579_4748.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                    (let uu____4980 =
=======
                    (let uu____4947 =
>>>>>>> single tentative commit which could be reverted later
=======
                    (let uu____4952 =
>>>>>>> snap
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
=======
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11  in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21  in
                     debug1
                       (fun uu____3039  ->
                          let uu____3040 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____3042 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____3047 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____3040 uu____3042 uu____3047);
                     (let aux uu____3065 =
                        let uu____3066 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____3066
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____3097 ->
                              let uu____3098 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____3098
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____3130 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____3130
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____3175 =
                        let uu____3176 =
                          let uu____3178 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____3178  in
                        if uu____3176
                        then
                          let uu____3192 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____3192
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____3215 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____3215))
                        else
                          (let uu____3230 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____3230
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___481_3272 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___481_3272.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___481_3272.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____3273 =
                                 let uu____3279 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____3279, reason)  in
                               FStar_Util.Inl uu____3273  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____3315 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____3315
                                   (close1 x "c1 Tot")
                             | (uu____3329,FStar_Pervasives_Native.Some x) ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____3352,uu____3353) -> aux ()
                           else
                             (let uu____3368 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____3368
                              then
                                let uu____3381 =
                                  let uu____3387 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____3387, "both GTot")  in
                                FStar_Util.Inl uu____3381
                              else aux ()))
                         in
                      let uu____3398 = try_simplify ()  in
                      match uu____3398 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____3424  ->
                                let uu____3425 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____3425);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____3439  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____3461 = lift_and_destruct env c11 c21
                                 in
                              match uu____3461 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
                                              let uu___659_5271 = x  in
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___659_5271.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
                                                  (uu___659_5271.FStar_Syntax_Syntax.index);
=======
                                              let uu___649_5238 = x  in
=======
                                              let uu___650_5243 = x  in
>>>>>>> snap
                                              {
                                                FStar_Syntax_Syntax.ppname =
                                                  (uu___650_5243.FStar_Syntax_Syntax.ppname);
                                                FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                                                  (uu___649_5238.FStar_Syntax_Syntax.index);
>>>>>>> single tentative commit which could be reverted later
=======
                                                  (uu___650_5243.FStar_Syntax_Syntax.index);
>>>>>>> snap
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
<<<<<<< HEAD
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
<<<<<<< HEAD
<<<<<<< HEAD
                     let uu___773_5908 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___773_5908.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___773_5908.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___773_5908.FStar_Syntax_Syntax.effect_args);
=======
                     let uu___763_5875 = retc1  in
=======
                     let uu___764_5880 = retc1  in
>>>>>>> snap
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___764_5880.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___764_5880.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
<<<<<<< HEAD
                         (uu___763_5875.FStar_Syntax_Syntax.effect_args);
>>>>>>> single tentative commit which could be reverted later
=======
                         (uu___764_5880.FStar_Syntax_Syntax.effect_args);
>>>>>>> snap
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
=======
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____4007 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____4011 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____4011
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____4017 =
              let uu____4019 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____4019  in
            (if uu____4017
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___600_4026 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___600_4026.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___600_4026.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___600_4026.FStar_Syntax_Syntax.effect_args);
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
               let uu____4039 =
                 let uu____4040 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
>>>>>>> snap
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
                      uu____6042.FStar_Syntax_Syntax.conjunction  in
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
                                            md.FStar_Syntax_Syntax.is_layered
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____7944 =
                                          let uu____7949 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____7949
                                           in
                                        (match uu____7944 with
                                         | (c,g_conjunction) ->
                                             let uu____7960 =
                                               let uu____7961 =
                                                 let uu____7962 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____7962 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____7961 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____7960)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____7663 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____7996::[] -> (comp, g_comp)
                      | uu____8039 ->
                          let uu____8056 =
                            let uu____8058 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            uu____8058.FStar_Syntax_Syntax.is_layered  in
                          if uu____8056
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
                             let uu____8070 = destruct_wp_comp comp1  in
                             match uu____8070 with
                             | (uu____8081,uu____8082,wp) ->
                                 let uu____8084 =
                                   FStar_Syntax_Util.get_match_with_close_wps
                                     md1.FStar_Syntax_Syntax.match_wps
                                    in
                                 (match uu____8084 with
                                  | (uu____8095,ite_wp,uu____8097) ->
                                      let wp1 =
                                        let uu____8101 =
                                          let uu____8106 =
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              [u_res_t] env md1 ite_wp
                                             in
                                          let uu____8107 =
                                            let uu____8108 =
                                              FStar_Syntax_Syntax.as_arg
                                                res_t
                                               in
                                            let uu____8117 =
                                              let uu____8128 =
                                                FStar_Syntax_Syntax.as_arg wp
                                                 in
                                              [uu____8128]  in
                                            uu____8108 :: uu____8117  in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            uu____8106 uu____8107
                                           in
                                        uu____8101
                                          FStar_Pervasives_Native.None
                                          wp.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____8161 =
                                        mk_comp md1 u_res_t res_t wp1
                                          bind_cases_flags
                                         in
                                      (uu____8161, g_comp)))))
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
          let uu____8195 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____8195 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____8211 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____8217 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____8211 uu____8217
              else
                (let uu____8226 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____8232 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____8226 uu____8232)
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
          let uu____8257 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____8257
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____8260 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____8260
        then u_res
        else
          (let is_total =
             let uu____8267 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____8267
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____8278 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____8278 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8281 =
                    let uu____8287 =
                      let uu____8289 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____8289
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____8287)
                     in
                  FStar_Errors.raise_error uu____8281
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
      let uu____8313 = destruct_wp_comp ct  in
      match uu____8313 with
      | (u_t,t,wp) ->
          let vc =
            let uu____8332 = FStar_TypeChecker_Env.get_range env  in
            let uu____8333 =
              let uu____8338 =
                let uu____8339 =
                  FStar_All.pipe_right md.FStar_Syntax_Syntax.trivial
                    FStar_Util.must
                   in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____8339
                 in
              let uu____8342 =
                let uu____8343 = FStar_Syntax_Syntax.as_arg t  in
                let uu____8352 =
                  let uu____8363 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____8363]  in
                uu____8343 :: uu____8352  in
              FStar_Syntax_Syntax.mk_Tm_app uu____8338 uu____8342  in
            uu____8333 FStar_Pervasives_Native.None uu____8332  in
          let uu____8396 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____8396)
  
let (maybe_coerce_bool_to_type :
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
          if env.FStar_TypeChecker_Env.is_pattern
          then (e, lc)
          else
            (let is_type1 t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____8437 =
                 let uu____8438 = FStar_Syntax_Subst.compress t2  in
                 uu____8438.FStar_Syntax_Syntax.n  in
               match uu____8437 with
               | FStar_Syntax_Syntax.Tm_type uu____8442 -> true
               | uu____8444 -> false  in
             let uu____8446 =
               let uu____8447 =
                 FStar_Syntax_Util.unrefine
                   lc.FStar_TypeChecker_Common.res_typ
                  in
               uu____8447.FStar_Syntax_Syntax.n  in
             match uu____8446 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____8455 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____8465 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____8465
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____8468 =
                     let uu____8469 =
                       let uu____8470 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____8470
                        in
                     (FStar_Pervasives_Native.None, uu____8469)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____8468
                    in
                 let e1 =
                   let uu____8476 =
                     let uu____8481 =
                       let uu____8482 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____8482]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____8481  in
                   uu____8476 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____8507 -> (e, lc))
  
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
          (let uu____8542 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____8542
           then
             let uu____8545 = FStar_Syntax_Print.term_to_string e  in
             let uu____8547 = FStar_TypeChecker_Common.lcomp_to_string lc  in
             let uu____8549 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____8545 uu____8547 uu____8549
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____8559 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____8559 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____8584 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____8610 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____8610, false)
             else
               (let uu____8620 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____8620, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____8633) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____8645 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____8645
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                    ((let uu___1020_8536 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1020_8536.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1020_8536.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1020_8536.FStar_TypeChecker_Common.comp_thunk)
=======
                    ((let uu___764_5396 = lc  in
=======
                    ((let uu___765_5396 = lc  in
>>>>>>> snap
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___765_5396.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___765_5396.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
<<<<<<< HEAD
                          (uu___764_5396.FStar_Syntax_Syntax.comp_thunk)
>>>>>>> snap
=======
                    ((let uu___1053_8629 = lc  in
=======
                    ((let uu___1053_8630 = lc  in
>>>>>>> cp
=======
                    ((let uu___1042_8597 = lc  in
>>>>>>> single tentative commit which could be reverted later
=======
                    ((let uu___1043_8602 = lc  in
>>>>>>> snap
=======
                    ((let uu___1047_8661 = lc  in
>>>>>>> nits
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1047_8661.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1047_8661.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                          (uu___1053_8629.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> snap
=======
                          (uu___765_5396.FStar_Syntax_Syntax.comp_thunk)
>>>>>>> snap
=======
                          (uu___1053_8630.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> cp
=======
                          (uu___1042_8597.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> single tentative commit which could be reverted later
=======
                          (uu___1043_8602.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> snap
=======
                          (uu___1047_8661.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> nits
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____8668 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____8668 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____8684 =
                      let uu____8685 = FStar_TypeChecker_Common.lcomp_comp lc
                         in
                      match uu____8685 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____8705 =
                            let uu____8707 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____8707 = FStar_Syntax_Util.Equal  in
                          if uu____8705
                          then
                            ((let uu____8714 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____8714
                              then
                                let uu____8718 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____8720 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____8718 uu____8720
                              else ());
                             (let uu____8725 = set_result_typ1 c  in
                              (uu____8725, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____8732 ->
                                   true
                               | uu____8740 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____8749 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____8749
                                  in
                               let lc1 =
                                 let uu____8751 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____8752 =
                                   let uu____8753 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____8753)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____8751 uu____8752
                                  in
                               ((let uu____8757 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____8757
                                 then
                                   let uu____8761 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____8763 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____8765 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____8767 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____8761 uu____8763 uu____8765
                                     uu____8767
                                 else ());
                                (let uu____8772 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____8772 with
                                 | (c1,g_lc) ->
                                     let uu____8783 = set_result_typ1 c1  in
                                     let uu____8784 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____8783, uu____8784)))
                             else
                               ((let uu____8788 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____8788
                                 then
                                   let uu____8792 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____8794 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____8792 uu____8794
                                 else ());
                                (let uu____8799 = set_result_typ1 c  in
                                 (uu____8799, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                      let uu___1057_8678 = g  in
=======
                      let uu___796_5502 = g  in
>>>>>>> snap
=======
                      let uu___1090_8771 = g  in
>>>>>>> snap
=======
                      let uu___797_5502 = g  in
>>>>>>> snap
=======
                      let uu___1090_8772 = g  in
>>>>>>> cp
=======
                      let uu___1079_8739 = g  in
>>>>>>> single tentative commit which could be reverted later
=======
                      let uu___1080_8744 = g  in
>>>>>>> snap
=======
                      let uu___1084_8803 = g  in
>>>>>>> nits
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
<<<<<<< HEAD
                        FStar_TypeChecker_Common.deferred =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                          (uu___1057_8678.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1057_8678.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1057_8678.FStar_TypeChecker_Common.implicits)
=======
                        FStar_TypeChecker_Env.deferred =
                          (uu___797_5502.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___797_5502.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
<<<<<<< HEAD
                          (uu___796_5502.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                          (uu___1090_8771.FStar_TypeChecker_Common.deferred);
=======
                          (uu___1090_8772.FStar_TypeChecker_Common.deferred);
>>>>>>> cp
=======
                          (uu___1079_8739.FStar_TypeChecker_Common.deferred);
>>>>>>> single tentative commit which could be reverted later
=======
                          (uu___1080_8744.FStar_TypeChecker_Common.deferred);
>>>>>>> snap
=======
                          (uu___1084_8803.FStar_TypeChecker_Common.deferred);
>>>>>>> nits
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1084_8803.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                          (uu___1090_8771.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
=======
                          (uu___797_5502.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                          (uu___1090_8772.FStar_TypeChecker_Common.implicits)
>>>>>>> cp
=======
                          (uu___1079_8739.FStar_TypeChecker_Common.implicits)
>>>>>>> single tentative commit which could be reverted later
=======
                          (uu___1080_8744.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
=======
                          (uu___1084_8803.FStar_TypeChecker_Common.implicits)
>>>>>>> nits
                      }  in
                    let strengthen uu____8813 =
                      let uu____8814 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____8814
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____8824 =
                           let uu____8825 = FStar_Syntax_Subst.compress f1
                              in
                           uu____8825.FStar_Syntax_Syntax.n  in
                         match uu____8824 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____8832,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____8834;
                                           FStar_Syntax_Syntax.vars =
                                             uu____8835;_},uu____8836)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                               let uu___1073_8737 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1073_8737.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1073_8737.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1073_8737.FStar_TypeChecker_Common.comp_thunk)
=======
                               let uu___1106_8830 = lc  in
=======
                               let uu___1106_8831 = lc  in
>>>>>>> cp
=======
                               let uu___1095_8798 = lc  in
>>>>>>> single tentative commit which could be reverted later
=======
                               let uu___1096_8803 = lc  in
>>>>>>> snap
=======
                               let uu___1100_8862 = lc  in
>>>>>>> nits
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1100_8862.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1100_8862.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                   (uu___1106_8830.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> snap
=======
                                   (uu___1106_8831.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> cp
=======
                                   (uu___1095_8798.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> single tentative commit which could be reverted later
=======
                                   (uu___1096_8803.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> snap
=======
                                   (uu___1100_8862.FStar_TypeChecker_Common.comp_thunk)
>>>>>>> nits
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____8863 ->
                             let uu____8864 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____8864 with
                              | (c,g_c) ->
                                  ((let uu____8876 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____8876
                                    then
                                      let uu____8880 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____8882 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____8884 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____8886 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____8880 uu____8882 uu____8884
                                        uu____8886
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
                                        let uu____8899 =
                                          let uu____8904 =
                                            let uu____8905 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____8905]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____8904
                                           in
                                        uu____8899
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____8932 =
                                      let uu____8937 =
                                        FStar_All.pipe_left
                                          (fun _8958  ->
                                             FStar_Pervasives_Native.Some
                                               _8958)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____8959 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____8960 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____8961 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____8937
                                        uu____8959 e uu____8960 uu____8961
                                       in
                                    match uu____8932 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                          let uu___1091_8844 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1091_8844.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1091_8844.FStar_Syntax_Syntax.index);
=======
                                          let uu___1124_8937 = x  in
=======
                                          let uu___1124_8938 = x  in
>>>>>>> cp
=======
                                          let uu___1113_8905 = x  in
>>>>>>> single tentative commit which could be reverted later
=======
                                          let uu___1114_8910 = x  in
>>>>>>> snap
=======
                                          let uu___1118_8969 = x  in
>>>>>>> nits
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1118_8969.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                              (uu___1124_8937.FStar_Syntax_Syntax.index);
>>>>>>> snap
=======
                                              (uu___1124_8938.FStar_Syntax_Syntax.index);
>>>>>>> cp
=======
                                              (uu___1113_8905.FStar_Syntax_Syntax.index);
>>>>>>> single tentative commit which could be reverted later
=======
                                              (uu___1114_8910.FStar_Syntax_Syntax.index);
>>>>>>> snap
=======
                                              (uu___1118_8969.FStar_Syntax_Syntax.index);
>>>>>>> nits
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____8971 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____8971
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____8974 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____8974 with
                                         | (c2,g_lc) ->
                                             ((let uu____8986 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____8986
                                               then
                                                 let uu____8990 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____8990
                                               else ());
                                              (let uu____8995 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                               (c2, uu____8870))))))))
=======
                               let uu___812_5549 = lc  in
=======
                               let uu___813_5549 = lc  in
>>>>>>> snap
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___813_5549.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___813_5549.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___813_5549.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____5550 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____5553 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____5553
                               then
                                 let uu____5557 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____5559 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____5561 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____5563 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____5557 uu____5559 uu____5561
                                   uu____5563
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
                                   let uu____5576 =
                                     let uu____5581 =
                                       let uu____5582 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____5582]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____5581
                                      in
                                   uu____5576 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____5609 =
                                 let uu____5614 =
                                   FStar_All.pipe_left
                                     (fun _5635  ->
                                        FStar_Pervasives_Native.Some _5635)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____5636 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____5637 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____5638 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____5614
                                   uu____5636 e uu____5637 uu____5638
                                  in
                               match uu____5609 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___829_5642 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___829_5642.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___829_5642.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____5644 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____5644
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____5649 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____5649
                                     then
                                       let uu____5653 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____5653
                                     else ());
                                    c2))))
>>>>>>> snap
=======
                                               (c2, uu____8963))))))))
>>>>>>> snap
=======
                                               (c2, uu____8964))))))))
>>>>>>> cp
=======
                                               (c2, uu____8931))))))))
>>>>>>> single tentative commit which could be reverted later
=======
                                               (c2, uu____8936))))))))
>>>>>>> snap
=======
                                               (c2, uu____8995))))))))
>>>>>>> nits
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_9004  ->
                              match uu___6_9004 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____9007 -> []))
                       in
                    let lc1 =
                      let uu____9009 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____9009 t flags
                        strengthen
                       in
                    let g2 =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                      let uu___1107_8886 = g1  in
=======
                      let uu___842_5673 = g1  in
>>>>>>> snap
=======
                      let uu___1140_8979 = g1  in
>>>>>>> snap
=======
                      let uu___843_5673 = g1  in
>>>>>>> snap
=======
                      let uu___1140_8980 = g1  in
>>>>>>> cp
=======
                      let uu___1129_8947 = g1  in
>>>>>>> single tentative commit which could be reverted later
=======
                      let uu___1130_8952 = g1  in
>>>>>>> snap
=======
                      let uu___1134_9011 = g1  in
>>>>>>> nits
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
<<<<<<< HEAD
                        FStar_TypeChecker_Common.deferred =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                          (uu___1107_8886.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1107_8886.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1107_8886.FStar_TypeChecker_Common.implicits)
=======
                        FStar_TypeChecker_Env.deferred =
                          (uu___843_5673.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___843_5673.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
<<<<<<< HEAD
                          (uu___842_5673.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                          (uu___1140_8979.FStar_TypeChecker_Common.deferred);
=======
                          (uu___1140_8980.FStar_TypeChecker_Common.deferred);
>>>>>>> cp
=======
                          (uu___1129_8947.FStar_TypeChecker_Common.deferred);
>>>>>>> single tentative commit which could be reverted later
=======
                          (uu___1130_8952.FStar_TypeChecker_Common.deferred);
>>>>>>> snap
=======
                          (uu___1134_9011.FStar_TypeChecker_Common.deferred);
>>>>>>> nits
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1134_9011.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                          (uu___1140_8979.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
=======
                          (uu___843_5673.FStar_TypeChecker_Env.implicits)
>>>>>>> snap
=======
                          (uu___1140_8980.FStar_TypeChecker_Common.implicits)
>>>>>>> cp
=======
                          (uu___1129_8947.FStar_TypeChecker_Common.implicits)
>>>>>>> single tentative commit which could be reverted later
=======
                          (uu___1130_8952.FStar_TypeChecker_Common.implicits)
>>>>>>> snap
=======
                          (uu___1134_9011.FStar_TypeChecker_Common.implicits)
>>>>>>> nits
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
        let uu____9047 =
          let uu____9050 =
            let uu____9055 =
              let uu____9056 =
                let uu____9065 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____9065  in
              [uu____9056]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____9055  in
          uu____9050 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____9047  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____9088 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____9088
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____9107 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____9123 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____9140 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____9140
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____9156)::(ens,uu____9158)::uu____9159 ->
                    let uu____9202 =
                      let uu____9205 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____9205  in
                    let uu____9206 =
                      let uu____9207 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____9207  in
                    (uu____9202, uu____9206)
                | uu____9210 ->
                    let uu____9221 =
                      let uu____9227 =
                        let uu____9229 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____9229
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____9227)
                       in
                    FStar_Errors.raise_error uu____9221
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____9249)::uu____9250 ->
                    let uu____9277 =
                      let uu____9282 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____9282
                       in
                    (match uu____9277 with
                     | (us_r,uu____9314) ->
                         let uu____9315 =
                           let uu____9320 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____9320
                            in
                         (match uu____9315 with
                          | (us_e,uu____9352) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____9355 =
                                  let uu____9356 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____9356
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____9355
                                  us_r
                                 in
                              let as_ens =
                                let uu____9358 =
                                  let uu____9359 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____9359
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____9358
                                  us_e
                                 in
                              let req =
                                let uu____9363 =
                                  let uu____9368 =
                                    let uu____9369 =
                                      let uu____9380 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9380]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____9369
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____9368
                                   in
                                uu____9363 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____9420 =
                                  let uu____9425 =
                                    let uu____9426 =
                                      let uu____9437 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9437]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____9426
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____9425
                                   in
                                uu____9420 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____9474 =
                                let uu____9477 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____9477  in
                              let uu____9478 =
                                let uu____9479 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____9479  in
                              (uu____9474, uu____9478)))
                | uu____9482 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
<<<<<<< HEAD
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
=======
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
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta] env tm
         in
      (let uu____6178 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____6178
       then
         let uu____6183 = FStar_Syntax_Print.term_to_string tm  in
         let uu____6185 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6183 uu____6185
       else ());
      tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
>>>>>>> snap
  =
  fun env  ->
    fun steps  ->
      fun t  ->
        let tm = FStar_Syntax_Util.mk_reify t  in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
<<<<<<< HEAD
            (FStar_List.append
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.EraseUniverses;
               FStar_TypeChecker_Env.AllowUnboundUniverses] steps) env tm
=======
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Eager_unfolding;
            FStar_TypeChecker_Env.EraseUniverses;
            FStar_TypeChecker_Env.AllowUnboundUniverses;
            FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta] env tm
>>>>>>> snap
           in
        (let uu____9521 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____9521
         then
           let uu____9526 = FStar_Syntax_Print.term_to_string tm  in
           let uu____9528 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____9526
             uu____9528
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
                 FStar_TypeChecker_Env.AllowUnboundUniverses] steps) env tm
             in
          (let uu____9587 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____9587
           then
             let uu____9592 = FStar_Syntax_Print.term_to_string tm  in
             let uu____9594 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____9592
               uu____9594
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____9605 =
      let uu____9607 =
        let uu____9608 = FStar_Syntax_Subst.compress t  in
        uu____9608.FStar_Syntax_Syntax.n  in
      match uu____9607 with
      | FStar_Syntax_Syntax.Tm_app uu____9612 -> false
      | uu____9630 -> true  in
    if uu____9605
    then t
    else
      (let uu____9635 = FStar_Syntax_Util.head_and_args t  in
       match uu____9635 with
       | (head1,args) ->
           let uu____9678 =
             let uu____9680 =
               let uu____9681 = FStar_Syntax_Subst.compress head1  in
               uu____9681.FStar_Syntax_Syntax.n  in
             match uu____9680 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____9686 -> false  in
           if uu____9678
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____9718 ->
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
          ((let uu____9765 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____9765
            then
              let uu____9768 = FStar_Syntax_Print.term_to_string e  in
              let uu____9770 = FStar_Syntax_Print.term_to_string t  in
              let uu____9772 =
                let uu____9774 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____9774
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____9768 uu____9770 uu____9772
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____9787 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____9787 with
              | (formals,uu____9803) ->
                  let n_implicits =
                    let uu____9825 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____9903  ->
                              match uu____9903 with
                              | (uu____9911,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____9918 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____9918 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____9825 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____10043 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____10043 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____10057 =
                      let uu____10063 =
                        let uu____10065 = FStar_Util.string_of_int n_expected
                           in
                        let uu____10067 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____10069 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____10065 uu____10067 uu____10069
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____10063)
                       in
                    let uu____10073 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____10057 uu____10073
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_10091 =
              match uu___7_10091 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____10134 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____10134 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _10265,uu____10252)
                           when _10265 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____10298,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____10300))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____10334 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____10334 with
                            | (v1,uu____10375,g) ->
                                ((let uu____10390 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____10390
                                  then
                                    let uu____10393 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____10393
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____10403 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____10403 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____10496 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____10496))))
                       | (uu____10523,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____10560 =
                             let uu____10573 =
                               let uu____10580 =
                                 let uu____10585 = FStar_Dyn.mkdyn env  in
                                 (uu____10585, tau)  in
                               FStar_Pervasives_Native.Some uu____10580  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____10573
                              in
                           (match uu____10560 with
                            | (v1,uu____10618,g) ->
                                ((let uu____10633 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____10633
                                  then
                                    let uu____10636 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____10636
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____10646 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____10646 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____10739 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____10739))))
                       | (uu____10766,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____10814 =
                       let uu____10841 = inst_n_binders t1  in
                       aux [] uu____10841 bs1  in
                     (match uu____10814 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____10913) -> (e, torig, guard)
                           | (uu____10944,[]) when
                               let uu____10975 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____10975 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____10977 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____11005 ->
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
            | uu____11018 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____11030 =
      let uu____11034 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____11034
        (FStar_List.map
           (fun u  ->
              let uu____11046 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____11046 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____11030 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____11074 = FStar_Util.set_is_empty x  in
      if uu____11074
      then []
      else
        (let s =
           let uu____11092 =
             let uu____11095 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____11095  in
           FStar_All.pipe_right uu____11092 FStar_Util.set_elements  in
         (let uu____11111 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____11111
          then
            let uu____11116 =
              let uu____11118 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____11118  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____11116
          else ());
         (let r =
            let uu____11127 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____11127  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____11166 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____11166
                     then
                       let uu____11171 =
                         let uu____11173 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____11173
                          in
                       let uu____11177 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____11179 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____11171 uu____11177 uu____11179
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
        let uu____11209 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____11209 FStar_Util.set_elements  in
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
        | ([],uu____11248) -> generalized_univ_names
        | (uu____11255,[]) -> explicit_univ_names
        | uu____11262 ->
            let uu____11271 =
              let uu____11277 =
                let uu____11279 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____11279
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____11277)
               in
            FStar_Errors.raise_error uu____11271 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____11301 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____11301
       then
         let uu____11306 = FStar_Syntax_Print.term_to_string t  in
         let uu____11308 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____11306 uu____11308
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____11317 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____11317
        then
          let uu____11322 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____11322
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____11331 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____11331
         then
           let uu____11336 = FStar_Syntax_Print.term_to_string t  in
           let uu____11338 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____11336 uu____11338
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
        let uu____11422 =
          let uu____11424 =
            FStar_Util.for_all
              (fun uu____11438  ->
                 match uu____11438 with
                 | (uu____11448,uu____11449,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____11424  in
        if uu____11422
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____11501 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____11501
              then
                let uu____11504 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____11504
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____11511 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____11511
               then
                 let uu____11514 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____11514
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____11532 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____11532 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____11566 =
             match uu____11566 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____11603 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____11603
                   then
                     let uu____11608 =
                       let uu____11610 =
                         let uu____11614 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____11614
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____11610
                         (FStar_String.concat ", ")
                        in
                     let uu____11662 =
                       let uu____11664 =
                         let uu____11668 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____11668
                           (FStar_List.map
                              (fun u  ->
                                 let uu____11681 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____11683 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____11681
                                   uu____11683))
                          in
                       FStar_All.pipe_right uu____11664
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____11608
                       uu____11662
                   else ());
                  (let univs2 =
                     let uu____11697 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____11709 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____11709) univs1
                       uu____11697
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____11716 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____11716
                    then
                      let uu____11721 =
                        let uu____11723 =
                          let uu____11727 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____11727
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____11723
                          (FStar_String.concat ", ")
                         in
                      let uu____11775 =
                        let uu____11777 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____11791 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____11793 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____11791
                                    uu____11793))
                           in
                        FStar_All.pipe_right uu____11777
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____11721 uu____11775
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____11814 =
             let uu____11831 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____11831  in
           match uu____11814 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____11921 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____11921
                 then ()
                 else
                   (let uu____11926 = lec_hd  in
                    match uu____11926 with
                    | (lb1,uu____11934,uu____11935) ->
                        let uu____11936 = lec2  in
                        (match uu____11936 with
                         | (lb2,uu____11944,uu____11945) ->
                             let msg =
                               let uu____11948 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____11950 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____11948 uu____11950
                                in
                             let uu____11953 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____11953))
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
                 let uu____12021 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____12021
                 then ()
                 else
                   (let uu____12026 = lec_hd  in
                    match uu____12026 with
                    | (lb1,uu____12034,uu____12035) ->
                        let uu____12036 = lec2  in
                        (match uu____12036 with
                         | (lb2,uu____12044,uu____12045) ->
                             let msg =
                               let uu____12048 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____12050 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____12048 uu____12050
                                in
                             let uu____12053 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____12053))
                  in
               let lecs1 =
                 let uu____12064 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____12117 = univs_and_uvars_of_lec this_lec  in
                        match uu____12117 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____12064 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____12222 = lec_hd  in
                   match uu____12222 with
                   | (lbname,e,c) ->
                       let uu____12232 =
                         let uu____12238 =
                           let uu____12240 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____12242 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____12244 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____12240 uu____12242 uu____12244
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____12238)
                          in
                       let uu____12248 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____12232 uu____12248
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____12267 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____12267 with
                         | FStar_Pervasives_Native.Some uu____12276 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____12284 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____12288 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____12288 with
                              | (bs,kres) ->
                                  ((let uu____12332 =
                                      let uu____12333 =
                                        let uu____12336 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____12336
                                         in
                                      uu____12333.FStar_Syntax_Syntax.n  in
                                    match uu____12332 with
                                    | FStar_Syntax_Syntax.Tm_type uu____12337
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____12341 =
                                          let uu____12343 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____12343  in
                                        if uu____12341
                                        then fail1 kres
                                        else ()
                                    | uu____12348 -> fail1 kres);
                                   (let a =
                                      let uu____12350 =
                                        let uu____12353 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _12356  ->
                                             FStar_Pervasives_Native.Some
                                               _12356) uu____12353
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____12350
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____12364 ->
                                          let uu____12373 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____12373
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
                      (fun uu____12476  ->
                         match uu____12476 with
                         | (lbname,e,c) ->
                             let uu____12522 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____12583 ->
                                   let uu____12596 = (e, c)  in
                                   (match uu____12596 with
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
                                                (fun uu____12636  ->
                                                   match uu____12636 with
                                                   | (x,uu____12642) ->
                                                       let uu____12643 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____12643)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____12661 =
                                                let uu____12663 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____12663
                                                 in
                                              if uu____12661
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
                                          let uu____12672 =
                                            let uu____12673 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____12673.FStar_Syntax_Syntax.n
                                             in
                                          match uu____12672 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____12698 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____12698 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____12709 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____12713 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____12713, gen_tvars))
                                in
                             (match uu____12522 with
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
        (let uu____12860 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____12860
         then
           let uu____12863 =
             let uu____12865 =
               FStar_List.map
                 (fun uu____12880  ->
                    match uu____12880 with
                    | (lb,uu____12889,uu____12890) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____12865 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____12863
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____12916  ->
                match uu____12916 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____12945 = gen env is_rec lecs  in
           match uu____12945 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____13044  ->
                       match uu____13044 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____13106 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____13106
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____13154  ->
                           match uu____13154 with
                           | (l,us,e,c,gvs) ->
                               let uu____13188 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____13190 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____13192 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____13194 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____13196 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____13188 uu____13190 uu____13192
                                 uu____13194 uu____13196))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____13241  ->
                match uu____13241 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____13285 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____13285, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
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
              (let uu____13346 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____13346 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____13352 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _13355  -> FStar_Pervasives_Native.Some _13355)
                     uu____13352)
             in
          let is_var e1 =
            let uu____13363 =
              let uu____13364 = FStar_Syntax_Subst.compress e1  in
              uu____13364.FStar_Syntax_Syntax.n  in
            match uu____13363 with
            | FStar_Syntax_Syntax.Tm_name uu____13368 -> true
            | uu____13370 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                     (let uu___1563_13256 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1563_13256.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1563_13256.FStar_Syntax_Syntax.index);
=======
                     (let uu___1298_10043 = x  in
=======
                     (let uu___1299_10043 = x  in
>>>>>>> snap
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1299_10043.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
<<<<<<< HEAD
                          (uu___1298_10043.FStar_Syntax_Syntax.index);
>>>>>>> snap
=======
                     (let uu___1596_13349 = x  in
=======
                     (let uu___1596_13350 = x  in
>>>>>>> cp
=======
                     (let uu___1585_13317 = x  in
>>>>>>> single tentative commit which could be reverted later
=======
                     (let uu___1586_13322 = x  in
>>>>>>> snap
=======
                     (let uu___1590_13381 = x  in
>>>>>>> nits
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1590_13381.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                          (uu___1596_13349.FStar_Syntax_Syntax.index);
>>>>>>> snap
=======
                          (uu___1299_10043.FStar_Syntax_Syntax.index);
>>>>>>> snap
=======
                          (uu___1596_13350.FStar_Syntax_Syntax.index);
>>>>>>> cp
=======
                          (uu___1585_13317.FStar_Syntax_Syntax.index);
>>>>>>> single tentative commit which could be reverted later
=======
                          (uu___1586_13322.FStar_Syntax_Syntax.index);
>>>>>>> snap
=======
                          (uu___1590_13381.FStar_Syntax_Syntax.index);
>>>>>>> nits
=======
                     (let uu___1593_13391 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1593_13391.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1593_13391.FStar_Syntax_Syntax.index);
>>>>>>> snap
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____13392 -> e2  in
          let env2 =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
            let uu___1566_13259 = env1  in
            let uu____13260 =
=======
            let uu___1301_10046 = env1  in
=======
            let uu___1302_10046 = env1  in
>>>>>>> snap
            let uu____10047 =
>>>>>>> snap
=======
            let uu___1599_13352 = env1  in
            let uu____13353 =
>>>>>>> snap
=======
            let uu___1599_13353 = env1  in
            let uu____13354 =
>>>>>>> cp
=======
            let uu___1588_13320 = env1  in
            let uu____13321 =
>>>>>>> single tentative commit which could be reverted later
=======
            let uu___1589_13325 = env1  in
            let uu____13326 =
>>>>>>> snap
=======
            let uu___1593_13384 = env1  in
            let uu____13385 =
>>>>>>> nits
=======
            let uu___1596_13394 = env1  in
            let uu____13395 =
>>>>>>> snap
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                (uu___1566_13259.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1566_13259.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1566_13259.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1566_13259.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1566_13259.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1566_13259.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1566_13259.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1566_13259.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1566_13259.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1566_13259.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1566_13259.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1566_13259.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1566_13259.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1566_13259.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1566_13259.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1566_13259.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1566_13259.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____13260;
              FStar_TypeChecker_Env.is_iface =
                (uu___1566_13259.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1566_13259.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1566_13259.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1566_13259.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1566_13259.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1566_13259.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1566_13259.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1566_13259.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1566_13259.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1566_13259.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1566_13259.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1566_13259.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1566_13259.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1566_13259.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1566_13259.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1566_13259.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1566_13259.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                (uu___1493_12204.FStar_TypeChecker_Env.synth_hook);
=======
                (uu___1486_12242.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1486_12242.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1470_12026.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1470_12026.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1477_12144.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1477_12144.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1487_12280.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1487_12280.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1488_12306.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1488_12306.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1505_12328.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1505_12328.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1497_12138.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1497_12138.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1499_12153.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1499_12153.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1508_12202.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1508_12202.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                (uu___1566_13259.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1566_13259.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
              FStar_TypeChecker_Env.splice =
                (uu___1566_13259.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1566_13259.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1566_13259.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1566_13259.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1566_13259.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1566_13259.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1566_13259.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                (uu___1499_12153.FStar_TypeChecker_Env.strict_args_tab)
=======
                (uu___1300_10046.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1300_10046.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                (uu___1508_12202.FStar_TypeChecker_Env.strict_args_tab)
>>>>>>> snap
=======
                (uu___1566_13259.FStar_TypeChecker_Env.strict_args_tab)
>>>>>>> snap
=======
                (uu___1301_10046.FStar_TypeChecker_Env.solver);
=======
                (uu___1302_10046.FStar_TypeChecker_Env.solver);
>>>>>>> snap
              FStar_TypeChecker_Env.range =
                (uu___1302_10046.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1302_10046.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1302_10046.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1302_10046.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1302_10046.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1302_10046.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1302_10046.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1302_10046.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1302_10046.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1302_10046.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1302_10046.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1302_10046.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1302_10046.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1302_10046.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1302_10046.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1302_10046.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10047;
              FStar_TypeChecker_Env.is_iface =
                (uu___1302_10046.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1302_10046.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1302_10046.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1302_10046.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1302_10046.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1302_10046.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1302_10046.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1302_10046.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1302_10046.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1302_10046.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1302_10046.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1302_10046.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1302_10046.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1302_10046.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1302_10046.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1302_10046.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1302_10046.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1302_10046.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1302_10046.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1302_10046.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1302_10046.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1302_10046.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1302_10046.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1302_10046.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1302_10046.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1302_10046.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
<<<<<<< HEAD
                (uu___1301_10046.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                (uu___1599_13352.FStar_TypeChecker_Env.solver);
=======
                (uu___1599_13353.FStar_TypeChecker_Env.solver);
>>>>>>> cp
=======
                (uu___1588_13320.FStar_TypeChecker_Env.solver);
>>>>>>> single tentative commit which could be reverted later
=======
                (uu___1589_13325.FStar_TypeChecker_Env.solver);
>>>>>>> snap
=======
                (uu___1593_13384.FStar_TypeChecker_Env.solver);
>>>>>>> nits
              FStar_TypeChecker_Env.range =
                (uu___1593_13384.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1593_13384.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1593_13384.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1593_13384.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1593_13384.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1593_13384.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1593_13384.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1593_13384.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1593_13384.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1593_13384.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1593_13384.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1593_13384.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1593_13384.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1593_13384.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1593_13384.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1593_13384.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____13385;
              FStar_TypeChecker_Env.is_iface =
                (uu___1593_13384.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1593_13384.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1593_13384.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1593_13384.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1593_13384.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1593_13384.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1593_13384.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1593_13384.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1593_13384.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1593_13384.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1593_13384.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1593_13384.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1593_13384.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1593_13384.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1593_13384.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1593_13384.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1593_13384.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1593_13384.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1593_13384.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1593_13384.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1593_13384.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1593_13384.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1593_13384.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1593_13384.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1593_13384.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1593_13384.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1593_13384.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                (uu___1599_13352.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                (uu___1302_10046.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                (uu___1599_13353.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> cp
=======
                (uu___1588_13320.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> single tentative commit which could be reverted later
=======
                (uu___1589_13325.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                (uu___1593_13384.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> nits
=======
                (uu___1596_13394.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1596_13394.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1596_13394.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1596_13394.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1596_13394.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1596_13394.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1596_13394.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1596_13394.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1596_13394.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1596_13394.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1596_13394.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1596_13394.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1596_13394.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1596_13394.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1596_13394.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1596_13394.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1596_13394.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____13395;
              FStar_TypeChecker_Env.is_iface =
                (uu___1596_13394.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1596_13394.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1596_13394.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1596_13394.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1596_13394.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1596_13394.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1596_13394.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1596_13394.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1596_13394.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1596_13394.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1596_13394.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1596_13394.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1596_13394.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1596_13394.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1596_13394.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1596_13394.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1596_13394.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1596_13394.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1596_13394.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1596_13394.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1596_13394.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1596_13394.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1596_13394.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1596_13394.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1596_13394.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1596_13394.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1596_13394.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1596_13394.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
            }  in
          let uu____13397 = check1 env2 t1 t2  in
          match uu____13397 with
          | FStar_Pervasives_Native.None  ->
              let uu____13404 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____13410 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____13404 uu____13410
          | FStar_Pervasives_Native.Some g ->
              ((let uu____13417 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____13417
                then
                  let uu____13422 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____13422
                else ());
               (let uu____13428 = decorate e t2  in (uu____13428, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____13456 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____13456
         then
           let uu____13459 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____13459
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____13473 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____13473 with
         | (c,g_c) ->
             let uu____13485 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____13485
             then
               let uu____13493 =
                 let uu____13495 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____13495  in
               (uu____13493, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____13503 =
                    let uu____13504 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____13504
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____13503
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____13505 = check_trivial_precondition env c1  in
                match uu____13505 with
                | (ct,vc,g_pre) ->
                    ((let uu____13521 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____13521
                      then
                        let uu____13526 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____13526
                      else ());
                     (let uu____13531 =
                        let uu____13533 =
                          let uu____13534 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____13534  in
                        discharge uu____13533  in
                      let uu____13535 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____13531, uu____13535)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_13569 =
        match uu___8_13569 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____13579)::[] -> f fst1
        | uu____13604 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____13616 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____13616
          (fun _13617  -> FStar_TypeChecker_Common.NonTrivial _13617)
         in
      let op_or_e e =
        let uu____13628 =
          let uu____13629 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____13629  in
        FStar_All.pipe_right uu____13628
          (fun _13632  -> FStar_TypeChecker_Common.NonTrivial _13632)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _13639  -> FStar_TypeChecker_Common.NonTrivial _13639)
         in
      let op_or_t t =
        let uu____13650 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____13650
          (fun _13653  -> FStar_TypeChecker_Common.NonTrivial _13653)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _13660  -> FStar_TypeChecker_Common.NonTrivial _13660)
         in
      let short_op_ite uu___9_13666 =
        match uu___9_13666 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____13676)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____13703)::[] ->
            let uu____13744 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____13744
              (fun _13745  -> FStar_TypeChecker_Common.NonTrivial _13745)
        | uu____13746 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____13758 =
          let uu____13766 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____13766)  in
        let uu____13774 =
          let uu____13784 =
            let uu____13792 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____13792)  in
          let uu____13800 =
            let uu____13810 =
              let uu____13818 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____13818)  in
            let uu____13826 =
              let uu____13836 =
                let uu____13844 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____13844)  in
              let uu____13852 =
                let uu____13862 =
                  let uu____13870 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____13870)  in
                [uu____13862; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____13836 :: uu____13852  in
            uu____13810 :: uu____13826  in
          uu____13784 :: uu____13800  in
        uu____13758 :: uu____13774  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____13932 =
            FStar_Util.find_map table
              (fun uu____13947  ->
                 match uu____13947 with
                 | (x,mk1) ->
                     let uu____13964 = FStar_Ident.lid_equals x lid  in
                     if uu____13964
                     then
                       let uu____13969 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____13969
                     else FStar_Pervasives_Native.None)
             in
          (match uu____13932 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____13973 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____13981 =
      let uu____13982 = FStar_Syntax_Util.un_uinst l  in
      uu____13982.FStar_Syntax_Syntax.n  in
    match uu____13981 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____13987 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____14023)::uu____14024 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____14043 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____14052,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____14053))::uu____14054 -> bs
      | uu____14072 ->
          let uu____14073 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____14073 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____14077 =
                 let uu____14078 = FStar_Syntax_Subst.compress t  in
                 uu____14078.FStar_Syntax_Syntax.n  in
               (match uu____14077 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____14082) ->
                    let uu____14103 =
                      FStar_Util.prefix_until
                        (fun uu___10_14143  ->
                           match uu___10_14143 with
                           | (uu____14151,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____14152)) ->
                               false
                           | uu____14157 -> true) bs'
                       in
                    (match uu____14103 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____14193,uu____14194) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____14266,uu____14267) ->
                         let uu____14340 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____14360  ->
                                   match uu____14360 with
                                   | (x,uu____14369) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____14340
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____14418  ->
                                     match uu____14418 with
                                     | (x,i) ->
                                         let uu____14437 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____14437, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____14448 -> bs))
  
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
            let uu____14477 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____14477
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
          let uu____14508 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____14508
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
        (let uu____14551 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____14551
         then
           ((let uu____14556 = FStar_Ident.text_of_lid lident  in
             d uu____14556);
            (let uu____14558 = FStar_Ident.text_of_lid lident  in
             let uu____14560 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____14558 uu____14560))
         else ());
        (let fv =
           let uu____14566 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____14566
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
         let uu____14578 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
         ((let uu___1723_14445 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1723_14445.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1723_14445.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1723_14445.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1723_14445.FStar_Syntax_Syntax.sigattrs)
           }), uu____14443))
=======
         ((let uu___1456_11219 = sig_ctx  in
=======
         ((let uu___1457_11219 = sig_ctx  in
>>>>>>> snap
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1457_11219.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1457_11219.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1457_11219.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1457_11219.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___1457_11219.FStar_Syntax_Syntax.sigopts)
           }), uu____11217))
>>>>>>> snap
=======
         ((let uu___1756_14538 = sig_ctx  in
=======
         ((let uu___1756_14539 = sig_ctx  in
>>>>>>> cp
=======
         ((let uu___1745_14506 = sig_ctx  in
>>>>>>> single tentative commit which could be reverted later
=======
         ((let uu___1746_14511 = sig_ctx  in
>>>>>>> snap
=======
         ((let uu___1750_14570 = sig_ctx  in
>>>>>>> nits
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1750_14570.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1750_14570.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1750_14570.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
               (uu___1756_14538.FStar_Syntax_Syntax.sigattrs)
           }), uu____14536))
>>>>>>> snap
=======
               (uu___1756_14539.FStar_Syntax_Syntax.sigattrs)
           }), uu____14537))
>>>>>>> cp
=======
               (uu___1745_14506.FStar_Syntax_Syntax.sigattrs)
           }), uu____14504))
>>>>>>> single tentative commit which could be reverted later
=======
               (uu___1746_14511.FStar_Syntax_Syntax.sigattrs)
           }), uu____14509))
>>>>>>> snap
=======
               (uu___1750_14570.FStar_Syntax_Syntax.sigattrs)
           }), uu____14568))
>>>>>>> nits
=======
         ((let uu___1753_14580 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___1753_14580.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___1753_14580.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___1753_14580.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___1753_14580.FStar_Syntax_Syntax.sigattrs)
           }), uu____14578))
>>>>>>> snap
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_14598 =
        match uu___11_14598 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____14601 -> false  in
      let reducibility uu___12_14609 =
        match uu___12_14609 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____14616 -> false  in
      let assumption uu___13_14624 =
        match uu___13_14624 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____14628 -> false  in
      let reification uu___14_14636 =
        match uu___14_14636 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____14639 -> true
        | uu____14641 -> false  in
      let inferred uu___15_14649 =
        match uu___15_14649 with
        | FStar_Syntax_Syntax.Discriminator uu____14651 -> true
        | FStar_Syntax_Syntax.Projector uu____14653 -> true
        | FStar_Syntax_Syntax.RecordType uu____14659 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____14669 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____14682 -> false  in
      let has_eq uu___16_14690 =
        match uu___16_14690 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____14694 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____14773 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        | uu____14738 -> true  in
=======
        | uu____11419 -> true  in
=======
        | uu____14780 -> true  in
>>>>>>> snap
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
<<<<<<< HEAD
                  let uu____11452 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____11452))
=======
                  let uu____14813 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____14813))
>>>>>>> snap
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
<<<<<<< HEAD
                    (let uu____11483 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____11483
=======
                    (let uu____14844 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____14844
>>>>>>> snap
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
<<<<<<< HEAD
           | FStar_Syntax_Syntax.Sig_bundle uu____11503 ->
               let uu____11512 =
                 let uu____11514 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_11520  ->
                           match uu___17_11520 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____11523 -> false))
                    in
                 Prims.op_Negation uu____11514  in
               if uu____11512
=======
           | FStar_Syntax_Syntax.Sig_bundle uu____14864 ->
               let uu____14873 =
                 let uu____14875 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_14881  ->
                           match uu___17_14881 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____14884 -> false))
                    in
                 Prims.op_Negation uu____14875  in
               if uu____14873
>>>>>>> snap
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
<<<<<<< HEAD
           | FStar_Syntax_Syntax.Sig_declare_typ uu____11530 -> ()
           | uu____11537 ->
=======
           | FStar_Syntax_Syntax.Sig_declare_typ uu____14891 -> ()
           | uu____14898 ->
>>>>>>> snap
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions")
                 r)
        else ()  in
>>>>>>> snap
=======
        | uu____14739 -> true  in
>>>>>>> cp
=======
        | uu____14706 -> true  in
>>>>>>> single tentative commit which could be reverted later
=======
        | uu____14711 -> true  in
>>>>>>> snap
=======
        | uu____14770 -> true  in
>>>>>>> nits
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____14749 =
        let uu____14751 =
=======
      let uu____14750 =
        let uu____14752 =
>>>>>>> cp
=======
      let uu____14717 =
        let uu____14719 =
>>>>>>> single tentative commit which could be reverted later
=======
      let uu____14722 =
        let uu____14724 =
>>>>>>> snap
=======
      let uu____14781 =
        let uu____14783 =
>>>>>>> nits
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___17_14789  ->
                  match uu___17_14789 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____14792 -> false))
           in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        FStar_All.pipe_right uu____14751 Prims.op_Negation  in
      if uu____14749
=======
      let uu____11551 =
        let uu____11553 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_11559  ->
                  match uu___18_11559 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11562 -> false))
           in
        FStar_All.pipe_right uu____11553 Prims.op_Negation  in
      if uu____11551
>>>>>>> snap
=======
        FStar_All.pipe_right uu____14752 Prims.op_Negation  in
      if uu____14750
>>>>>>> cp
=======
        FStar_All.pipe_right uu____14719 Prims.op_Negation  in
      if uu____14717
>>>>>>> single tentative commit which could be reverted later
=======
        FStar_All.pipe_right uu____14724 Prims.op_Negation  in
      if uu____14722
>>>>>>> snap
=======
        FStar_All.pipe_right uu____14783 Prims.op_Negation  in
      if uu____14781
>>>>>>> nits
=======
      let uu____14912 =
        let uu____14914 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_14920  ->
                  match uu___18_14920 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____14923 -> false))
           in
        FStar_All.pipe_right uu____14914 Prims.op_Negation  in
      if uu____14912
>>>>>>> snap
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          let uu____14781 =
            let uu____14787 =
              let uu____14789 = FStar_Syntax_Print.quals_to_string quals  in
=======
          let uu____14782 =
            let uu____14788 =
              let uu____14790 = FStar_Syntax_Print.quals_to_string quals  in
>>>>>>> cp
=======
          let uu____14749 =
            let uu____14755 =
              let uu____14757 = FStar_Syntax_Print.quals_to_string quals  in
>>>>>>> single tentative commit which could be reverted later
=======
          let uu____14754 =
            let uu____14760 =
              let uu____14762 = FStar_Syntax_Print.quals_to_string quals  in
>>>>>>> snap
=======
          let uu____14813 =
            let uu____14819 =
              let uu____14821 = FStar_Syntax_Print.quals_to_string quals  in
>>>>>>> nits
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____14821 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____14819)  in
          FStar_Errors.raise_error uu____14813 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____14839 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____14847 =
            let uu____14849 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____14849  in
          if uu____14847 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14827),uu____14828) ->
              ((let uu____14840 =
=======
          let uu____11583 =
            let uu____11589 =
              let uu____11591 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11591 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11589)  in
          FStar_Errors.raise_error uu____11583 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____11609 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11617 =
            let uu____11619 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____11619  in
          if uu____11617 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11630),uu____11631) ->
              ((let uu____11643 =
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14828),uu____14829) ->
              ((let uu____14841 =
>>>>>>> cp
=======
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14795),uu____14796) ->
              ((let uu____14808 =
>>>>>>> single tentative commit which could be reverted later
=======
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14800),uu____14801) ->
              ((let uu____14813 =
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14859),uu____14860) ->
              ((let uu____14872 =
>>>>>>> nits
=======
          let uu____14944 =
            let uu____14950 =
              let uu____14952 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____14952 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____14950)  in
          FStar_Errors.raise_error uu____14944 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____14970 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____14978 =
            let uu____14980 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____14980  in
          if uu____14978 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____14991),uu____14992) ->
              ((let uu____15004 =
>>>>>>> snap
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                if uu____14840
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____14849 =
=======
                if uu____11643
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11652 =
>>>>>>> snap
=======
                if uu____14841
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____14850 =
>>>>>>> cp
=======
                if uu____14808
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____14817 =
>>>>>>> single tentative commit which could be reverted later
=======
                if uu____14813
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____14822 =
>>>>>>> snap
=======
                if uu____14872
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____14881 =
>>>>>>> nits
=======
                if uu____15004
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____15013 =
>>>>>>> snap
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                if uu____14849
=======
                if uu____11652
>>>>>>> snap
=======
                if uu____14850
>>>>>>> cp
=======
                if uu____14817
>>>>>>> single tentative commit which could be reverted later
=======
                if uu____14822
>>>>>>> snap
=======
                if uu____14881
>>>>>>> nits
=======
                if uu____15013
>>>>>>> snap
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          | FStar_Syntax_Syntax.Sig_bundle uu____14767 ->
              let uu____14776 =
                let uu____14778 =
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
                Prims.op_Negation uu____14778  in
              if uu____14776 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14788 ->
              let uu____14795 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14795 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14803 ->
              let uu____14810 =
                let uu____14812 =
=======
          | FStar_Syntax_Syntax.Sig_bundle uu____11541 ->
              ((let uu____11551 =
                  let uu____11553 =
=======
          | FStar_Syntax_Syntax.Sig_bundle uu____14860 ->
              ((let uu____14870 =
                  let uu____14872 =
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_bundle uu____11663 ->
              ((let uu____11673 =
                  let uu____11675 =
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_bundle uu____14861 ->
              ((let uu____14871 =
                  let uu____14873 =
>>>>>>> cp
=======
          | FStar_Syntax_Syntax.Sig_bundle uu____14828 ->
              ((let uu____14838 =
                  let uu____14840 =
>>>>>>> single tentative commit which could be reverted later
=======
          | FStar_Syntax_Syntax.Sig_bundle uu____14833 ->
              ((let uu____14843 =
                  let uu____14845 =
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_bundle uu____14892 ->
              ((let uu____14902 =
                  let uu____14904 =
>>>>>>> nits
=======
          | FStar_Syntax_Syntax.Sig_bundle uu____15024 ->
              ((let uu____15034 =
                  let uu____15036 =
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                  Prims.op_Negation uu____11553  in
                if uu____11551 then err'1 () else ());
               (let uu____11563 =
=======
                  Prims.op_Negation uu____11675  in
                if uu____11673 then err'1 () else ());
               (let uu____11685 =
>>>>>>> snap
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_11691  ->
                           match uu___19_11691 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
<<<<<<< HEAD
                           | uu____11572 -> false)))
=======
                  Prims.op_Negation uu____14872  in
                if uu____14870 then err'1 () else ());
               (let uu____14882 =
=======
                  Prims.op_Negation uu____14873  in
                if uu____14871 then err'1 () else ());
               (let uu____14883 =
>>>>>>> cp
=======
                  Prims.op_Negation uu____14840  in
                if uu____14838 then err'1 () else ());
               (let uu____14850 =
>>>>>>> single tentative commit which could be reverted later
=======
                  Prims.op_Negation uu____14845  in
                if uu____14843 then err'1 () else ());
               (let uu____14855 =
>>>>>>> snap
=======
                  Prims.op_Negation uu____14904  in
                if uu____14902 then err'1 () else ());
               (let uu____14914 =
>>>>>>> nits
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___18_14920  ->
                           match uu___18_14920 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                           | uu____14891 -> false)))
>>>>>>> snap
=======
                           | uu____11694 -> false)))
>>>>>>> snap
=======
                           | uu____14892 -> false)))
>>>>>>> cp
=======
                           | uu____14859 -> false)))
>>>>>>> single tentative commit which could be reverted later
=======
                           | uu____14864 -> false)))
>>>>>>> snap
=======
                           | uu____14923 -> false)))
>>>>>>> nits
=======
                  Prims.op_Negation uu____15036  in
                if uu____15034 then err'1 () else ());
               (let uu____15046 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_15052  ->
                           match uu___19_15052 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____15055 -> false)))
>>>>>>> snap
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                if uu____11563
=======
                if uu____14882
>>>>>>> snap
=======
                if uu____11685
>>>>>>> snap
=======
                if uu____14883
>>>>>>> cp
=======
                if uu____14850
>>>>>>> single tentative commit which could be reverted later
=======
                if uu____14855
>>>>>>> snap
=======
                if uu____14914
>>>>>>> nits
=======
                if uu____15046
>>>>>>> snap
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11578 ->
              let uu____11585 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____11585 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11593 ->
              let uu____11600 =
                let uu____11602 =
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14897 ->
              let uu____14904 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14904 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14912 ->
              let uu____14919 =
                let uu____14921 =
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11700 ->
              let uu____11707 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____11707 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11715 ->
              let uu____11722 =
                let uu____11724 =
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14898 ->
              let uu____14905 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14905 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14913 ->
              let uu____14920 =
                let uu____14922 =
>>>>>>> cp
=======
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14865 ->
              let uu____14872 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14872 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14880 ->
              let uu____14887 =
                let uu____14889 =
>>>>>>> single tentative commit which could be reverted later
=======
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14870 ->
              let uu____14877 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14877 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14885 ->
              let uu____14892 =
                let uu____14894 =
>>>>>>> snap
=======
          | FStar_Syntax_Syntax.Sig_declare_typ uu____14929 ->
              let uu____14936 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____14936 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____14944 ->
              let uu____14951 =
                let uu____14953 =
>>>>>>> nits
=======
          | FStar_Syntax_Syntax.Sig_declare_typ uu____15061 ->
              let uu____15068 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____15068 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____15076 ->
              let uu____15083 =
                let uu____15085 =
>>>>>>> snap
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                Prims.op_Negation uu____14812  in
              if uu____14810 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14822 ->
              let uu____14823 =
                let uu____14825 =
=======
                Prims.op_Negation uu____11602  in
              if uu____11600 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11612 ->
              let uu____11613 =
                let uu____11615 =
>>>>>>> snap
=======
                Prims.op_Negation uu____14921  in
              if uu____14919 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14931 ->
              let uu____14932 =
                let uu____14934 =
>>>>>>> snap
=======
                Prims.op_Negation uu____11724  in
              if uu____11722 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11734 ->
              let uu____11735 =
                let uu____11737 =
>>>>>>> snap
=======
                Prims.op_Negation uu____14922  in
              if uu____14920 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14932 ->
              let uu____14933 =
                let uu____14935 =
>>>>>>> cp
=======
                Prims.op_Negation uu____14889  in
              if uu____14887 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14899 ->
              let uu____14900 =
                let uu____14902 =
>>>>>>> single tentative commit which could be reverted later
=======
                Prims.op_Negation uu____14894  in
              if uu____14892 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14904 ->
              let uu____14905 =
                let uu____14907 =
>>>>>>> snap
=======
                Prims.op_Negation uu____14953  in
              if uu____14951 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14963 ->
              let uu____14964 =
                let uu____14966 =
>>>>>>> nits
=======
                Prims.op_Negation uu____15085  in
              if uu____15083 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____15095 ->
              let uu____15096 =
                let uu____15098 =
>>>>>>> snap
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                Prims.op_Negation uu____14825  in
              if uu____14823 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14835 ->
              let uu____14836 =
                let uu____14838 =
=======
                Prims.op_Negation uu____11615  in
              if uu____11613 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11625 ->
              let uu____11626 =
                let uu____11628 =
>>>>>>> snap
=======
                Prims.op_Negation uu____14934  in
              if uu____14932 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14944 ->
              let uu____14945 =
                let uu____14947 =
>>>>>>> snap
=======
                Prims.op_Negation uu____11737  in
              if uu____11735 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11747 ->
              let uu____11748 =
                let uu____11750 =
>>>>>>> snap
=======
                Prims.op_Negation uu____14935  in
              if uu____14933 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14945 ->
              let uu____14946 =
                let uu____14948 =
>>>>>>> cp
=======
                Prims.op_Negation uu____14902  in
              if uu____14900 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14912 ->
              let uu____14913 =
                let uu____14915 =
>>>>>>> single tentative commit which could be reverted later
=======
                Prims.op_Negation uu____14907  in
              if uu____14905 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14917 ->
              let uu____14918 =
                let uu____14920 =
>>>>>>> snap
=======
                Prims.op_Negation uu____14966  in
              if uu____14964 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14976 ->
              let uu____14977 =
                let uu____14979 =
>>>>>>> nits
=======
                Prims.op_Negation uu____15098  in
              if uu____15096 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15108 ->
              let uu____15109 =
                let uu____15111 =
>>>>>>> snap
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                Prims.op_Negation uu____14838  in
              if uu____14836 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14848 ->
              let uu____14861 =
                let uu____14863 =
=======
                Prims.op_Negation uu____11628  in
              if uu____11626 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11638 ->
              let uu____11651 =
                let uu____11653 =
>>>>>>> snap
=======
                Prims.op_Negation uu____14947  in
              if uu____14945 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14957 ->
              let uu____14970 =
                let uu____14972 =
>>>>>>> snap
=======
                Prims.op_Negation uu____11750  in
              if uu____11748 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11760 ->
              let uu____11773 =
                let uu____11775 =
>>>>>>> snap
=======
                Prims.op_Negation uu____14948  in
              if uu____14946 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14958 ->
              let uu____14971 =
                let uu____14973 =
>>>>>>> cp
=======
                Prims.op_Negation uu____14915  in
              if uu____14913 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14925 ->
              let uu____14938 =
                let uu____14940 =
>>>>>>> single tentative commit which could be reverted later
=======
                Prims.op_Negation uu____14920  in
              if uu____14918 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14930 ->
              let uu____14943 =
                let uu____14945 =
>>>>>>> snap
=======
                Prims.op_Negation uu____14979  in
              if uu____14977 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14989 ->
              let uu____15002 =
                let uu____15004 =
>>>>>>> nits
=======
                Prims.op_Negation uu____15111  in
              if uu____15109 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15121 ->
              let uu____15134 =
                let uu____15136 =
>>>>>>> snap
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                Prims.op_Negation uu____14863  in
              if uu____14861 then err'1 () else ()
          | uu____14873 -> ()))
=======
                Prims.op_Negation uu____11653  in
              if uu____11651 then err'1 () else ()
          | uu____11663 -> ()))
>>>>>>> snap
=======
                Prims.op_Negation uu____14972  in
              if uu____14970 then err'1 () else ()
          | uu____14982 -> ()))
>>>>>>> snap
=======
                Prims.op_Negation uu____11775  in
              if uu____11773 then err'1 () else ()
          | uu____11785 -> ()))
>>>>>>> snap
=======
                Prims.op_Negation uu____14973  in
              if uu____14971 then err'1 () else ()
          | uu____14983 -> ()))
>>>>>>> cp
=======
                Prims.op_Negation uu____14940  in
              if uu____14938 then err'1 () else ()
          | uu____14950 -> ()))
>>>>>>> single tentative commit which could be reverted later
=======
                Prims.op_Negation uu____14945  in
              if uu____14943 then err'1 () else ()
          | uu____14955 -> ()))
>>>>>>> snap
=======
                Prims.op_Negation uu____15004  in
              if uu____15002 then err'1 () else ()
          | uu____15014 -> ()))
>>>>>>> nits
=======
                Prims.op_Negation uu____15136  in
              if uu____15134 then err'1 () else ()
          | uu____15146 -> ()))
>>>>>>> snap
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let has_erased_for_extraction_attr fv =
        let uu____14896 =
          let uu____14901 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____14901
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____14896
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____14920 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____14920
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____14938 =
                          let uu____14939 = FStar_Syntax_Subst.compress t1
                             in
                          uu____14939.FStar_Syntax_Syntax.n  in
                        match uu____14938 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____14945 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____14971 =
          let uu____14972 = FStar_Syntax_Subst.compress t1  in
          uu____14972.FStar_Syntax_Syntax.n  in
        match uu____14971 with
        | FStar_Syntax_Syntax.Tm_type uu____14976 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____14979 ->
            let uu____14994 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____14994 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____15027 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____15027
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____15033;
               FStar_Syntax_Syntax.index = uu____15034;
               FStar_Syntax_Syntax.sort = t2;_},uu____15036)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____15045,uu____15046) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____15088::[]) ->
            let uu____15127 =
              let uu____15128 = FStar_Syntax_Util.un_uinst head1  in
              uu____15128.FStar_Syntax_Syntax.n  in
            (match uu____15127 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
<<<<<<< HEAD
<<<<<<< HEAD
             | uu____14027 -> false)
        | uu____14029 -> false
=======
      let rec aux_whnf env t1 =
        (FStar_TypeChecker_Env.non_informative env t1) ||
          (let uu____11696 =
             let uu____11697 = FStar_Syntax_Subst.compress t1  in
             uu____11697.FStar_Syntax_Syntax.n  in
           match uu____11696 with
           | FStar_Syntax_Syntax.Tm_arrow uu____11701 ->
               let uu____11716 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____11716 with
                | (bs,c) ->
                    let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                    (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c)))
           | FStar_Syntax_Syntax.Tm_refine
               ({ FStar_Syntax_Syntax.ppname = uu____11749;
                  FStar_Syntax_Syntax.index = uu____11750;
                  FStar_Syntax_Syntax.sort = t2;_},uu____11752)
               -> aux env t2
           | uu____11760 -> false)
>>>>>>> snap
=======
      let rec descend env t1 =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____11702 =
          let uu____11703 = FStar_Syntax_Subst.compress t1  in
          uu____11703.FStar_Syntax_Syntax.n  in
        match uu____11702 with
        | FStar_Syntax_Syntax.Tm_arrow uu____11707 ->
            let uu____11722 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____11722 with
=======
        let uu____15021 =
          let uu____15022 = FStar_Syntax_Subst.compress t1  in
          uu____15022.FStar_Syntax_Syntax.n  in
        match uu____15021 with
        | FStar_Syntax_Syntax.Tm_arrow uu____15026 ->
            let uu____15041 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____15041 with
>>>>>>> snap
=======
        let uu____11824 =
          let uu____11825 = FStar_Syntax_Subst.compress t1  in
          uu____11825.FStar_Syntax_Syntax.n  in
        match uu____11824 with
        | FStar_Syntax_Syntax.Tm_arrow uu____11829 ->
            let uu____11844 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____11844 with
>>>>>>> snap
=======
        let uu____15022 =
          let uu____15023 = FStar_Syntax_Subst.compress t1  in
          uu____15023.FStar_Syntax_Syntax.n  in
        match uu____15022 with
        | FStar_Syntax_Syntax.Tm_arrow uu____15027 ->
            let uu____15042 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____15042 with
>>>>>>> cp
=======
        let uu____14989 =
          let uu____14990 = FStar_Syntax_Subst.compress t1  in
          uu____14990.FStar_Syntax_Syntax.n  in
        match uu____14989 with
        | FStar_Syntax_Syntax.Tm_arrow uu____14994 ->
            let uu____15009 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____15009 with
>>>>>>> single tentative commit which could be reverted later
=======
        let uu____14994 =
          let uu____14995 = FStar_Syntax_Subst.compress t1  in
          uu____14995.FStar_Syntax_Syntax.n  in
        match uu____14994 with
        | FStar_Syntax_Syntax.Tm_arrow uu____14999 ->
            let uu____15014 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____15014 with
>>>>>>> snap
=======
        let uu____15053 =
          let uu____15054 = FStar_Syntax_Subst.compress t1  in
          uu____15054.FStar_Syntax_Syntax.n  in
        match uu____15053 with
        | FStar_Syntax_Syntax.Tm_arrow uu____15058 ->
            let uu____15073 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____15073 with
>>>>>>> nits
=======
        let uu____15185 =
          let uu____15186 = FStar_Syntax_Subst.compress t1  in
          uu____15186.FStar_Syntax_Syntax.n  in
        match uu____15185 with
        | FStar_Syntax_Syntax.Tm_arrow uu____15190 ->
            let uu____15205 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____15205 with
>>>>>>> snap
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
            ({ FStar_Syntax_Syntax.ppname = uu____11755;
               FStar_Syntax_Syntax.index = uu____11756;
               FStar_Syntax_Syntax.sort = t2;_},uu____11758)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____11767) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____11793) ->
=======
            ({ FStar_Syntax_Syntax.ppname = uu____15074;
               FStar_Syntax_Syntax.index = uu____15075;
               FStar_Syntax_Syntax.sort = t2;_},uu____15077)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____15086) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____15112) ->
>>>>>>> snap
=======
            ({ FStar_Syntax_Syntax.ppname = uu____11877;
               FStar_Syntax_Syntax.index = uu____11878;
               FStar_Syntax_Syntax.sort = t2;_},uu____11880)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____11889) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____11915) ->
>>>>>>> snap
=======
            ({ FStar_Syntax_Syntax.ppname = uu____15075;
               FStar_Syntax_Syntax.index = uu____15076;
               FStar_Syntax_Syntax.sort = t2;_},uu____15078)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____15087) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____15113) ->
>>>>>>> cp
=======
            ({ FStar_Syntax_Syntax.ppname = uu____15042;
               FStar_Syntax_Syntax.index = uu____15043;
               FStar_Syntax_Syntax.sort = t2;_},uu____15045)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____15054) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____15080) ->
>>>>>>> single tentative commit which could be reverted later
=======
            ({ FStar_Syntax_Syntax.ppname = uu____15047;
               FStar_Syntax_Syntax.index = uu____15048;
               FStar_Syntax_Syntax.sort = t2;_},uu____15050)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____15059) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____15085) ->
>>>>>>> snap
=======
            ({ FStar_Syntax_Syntax.ppname = uu____15106;
               FStar_Syntax_Syntax.index = uu____15107;
               FStar_Syntax_Syntax.sort = t2;_},uu____15109)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____15118) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____15144) ->
>>>>>>> nits
=======
            ({ FStar_Syntax_Syntax.ppname = uu____15238;
               FStar_Syntax_Syntax.index = uu____15239;
               FStar_Syntax_Syntax.sort = t2;_},uu____15241)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____15250) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____15276) ->
>>>>>>> snap
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        | uu____11783 -> false
>>>>>>> snap
=======
             | uu____14076 -> false)
        | uu____14078 -> false
>>>>>>> snap
=======
             | uu____15133 -> false)
        | uu____15135 -> false
>>>>>>> snap
=======
        | uu____11799 -> false
>>>>>>> snap
=======
        | uu____15118 -> false
>>>>>>> snap
=======
        | uu____11921 -> false
>>>>>>> snap
=======
        | uu____15119 -> false
>>>>>>> cp
=======
        | uu____15086 -> false
>>>>>>> single tentative commit which could be reverted later
=======
        | uu____15091 -> false
>>>>>>> snap
=======
        | uu____15150 -> false
>>>>>>> nits
=======
        | uu____15282 -> false
>>>>>>> snap
      
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
<<<<<<< HEAD
        let res = aux_whnf env t2  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        (let uu____14039 =
=======
        (let uu____14088 =
>>>>>>> snap
=======
        (let uu____15145 =
>>>>>>> snap
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____15145
         then
           let uu____15150 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
<<<<<<< HEAD
<<<<<<< HEAD
             (if res then "true" else "false") uu____14044
=======
        (let uu____11770 =
=======
        let res =
          (FStar_TypeChecker_Env.non_informative env t2) || (descend env t2)
           in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        (let uu____11793 =
>>>>>>> snap
=======
        (let uu____11809 =
>>>>>>> snap
=======
        (let uu____11931 =
>>>>>>> snap
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____11931
         then
           let uu____11936 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
             (if res then "true" else "false") uu____11775
>>>>>>> snap
=======
             (if res then "true" else "false") uu____11798
>>>>>>> snap
=======
             (if res then "true" else "false") uu____14093
>>>>>>> snap
=======
             (if res then "true" else "false") uu____15150
>>>>>>> snap
=======
             (if res then "true" else "false") uu____11814
>>>>>>> snap
=======
        (let uu____15128 =
=======
        (let uu____15129 =
>>>>>>> cp
=======
        (let uu____15096 =
>>>>>>> single tentative commit which could be reverted later
=======
        (let uu____15101 =
>>>>>>> snap
=======
        (let uu____15160 =
>>>>>>> nits
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____15160
         then
           let uu____15165 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
             (if res then "true" else "false") uu____15133
>>>>>>> snap
=======
             (if res then "true" else "false") uu____11936
>>>>>>> snap
=======
             (if res then "true" else "false") uu____15134
>>>>>>> cp
=======
             (if res then "true" else "false") uu____15101
>>>>>>> single tentative commit which could be reverted later
=======
             (if res then "true" else "false") uu____15106
>>>>>>> snap
=======
             (if res then "true" else "false") uu____15165
>>>>>>> nits
=======
        (let uu____15292 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____15292
         then
           let uu____15297 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____15297
>>>>>>> snap
         else ());
        res
       in aux g t
  
<<<<<<< HEAD
let (fresh_non_layered_effect_repr :
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
            let wp_sort =
              let signature =
                FStar_TypeChecker_Env.lookup_effect_lid env eff_name  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
              let uu____15197 =
                let uu____15198 = FStar_Syntax_Subst.compress signature  in
                uu____15198.FStar_Syntax_Syntax.n  in
              match uu____15197 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15202) when
                  (FStar_List.length bs) = (Prims.of_int (2)) ->
                  let uu____15231 = FStar_Syntax_Subst.open_binders bs  in
                  (match uu____15231 with
                   | (a,uu____15233)::(wp,uu____15235)::[] ->
                       FStar_All.pipe_right wp.FStar_Syntax_Syntax.sort
                         (FStar_Syntax_Subst.subst
                            [FStar_Syntax_Syntax.NT (a, a_tm)]))
              | uu____15264 ->
                  let uu____15265 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name signature
                     in
                  FStar_Errors.raise_error uu____15265 r
               in
            let uu____15271 =
              let uu____15284 =
                let uu____15286 = FStar_Range.string_of_range r  in
                FStar_Util.format2 "implicit for wp of %s at %s"
                  eff_name.FStar_Ident.str uu____15286
                 in
              new_implicit_var uu____15284 r env wp_sort  in
            match uu____15271 with
            | (wp_uvar,uu____15294,g_wp_uvar) ->
                let eff_c =
                  let uu____15309 =
                    let uu____15310 =
                      let uu____15321 =
                        FStar_All.pipe_right wp_uvar
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____15321]  in
=======
              let uu____15180 =
                let uu____15181 = FStar_Syntax_Subst.compress signature  in
                uu____15181.FStar_Syntax_Syntax.n  in
              match uu____15180 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15185) when
=======
              let uu____15181 =
                let uu____15182 = FStar_Syntax_Subst.compress signature  in
                uu____15182.FStar_Syntax_Syntax.n  in
              match uu____15181 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15186) when
>>>>>>> cp
=======
              let uu____15148 =
                let uu____15149 = FStar_Syntax_Subst.compress signature  in
                uu____15149.FStar_Syntax_Syntax.n  in
              match uu____15148 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15153) when
>>>>>>> single tentative commit which could be reverted later
=======
              let uu____15153 =
                let uu____15154 = FStar_Syntax_Subst.compress signature  in
                uu____15154.FStar_Syntax_Syntax.n  in
              match uu____15153 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15158) when
>>>>>>> snap
=======
              let uu____15212 =
                let uu____15213 = FStar_Syntax_Subst.compress signature  in
                uu____15213.FStar_Syntax_Syntax.n  in
              match uu____15212 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15217) when
>>>>>>> nits
                  (FStar_List.length bs) = (Prims.of_int (2)) ->
                  let uu____15246 = FStar_Syntax_Subst.open_binders bs  in
                  (match uu____15246 with
                   | (a,uu____15248)::(wp,uu____15250)::[] ->
                       FStar_All.pipe_right wp.FStar_Syntax_Syntax.sort
                         (FStar_Syntax_Subst.subst
                            [FStar_Syntax_Syntax.NT (a, a_tm)]))
              | uu____15279 ->
                  let uu____15280 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name signature
                     in
                  FStar_Errors.raise_error uu____15280 r
               in
            let uu____15286 =
              let uu____15299 =
                let uu____15301 = FStar_Range.string_of_range r  in
                FStar_Util.format2 "implicit for wp of %s at %s"
                  eff_name.FStar_Ident.str uu____15301
                 in
              new_implicit_var uu____15299 r env wp_sort  in
            match uu____15286 with
            | (wp_uvar,uu____15309,g_wp_uvar) ->
                let eff_c =
                  let uu____15324 =
                    let uu____15325 =
                      let uu____15336 =
                        FStar_All.pipe_right wp_uvar
                          FStar_Syntax_Syntax.as_arg
                         in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                      [uu____15304]  in
>>>>>>> snap
=======
                      [uu____15305]  in
>>>>>>> cp
=======
                      [uu____15272]  in
>>>>>>> single tentative commit which could be reverted later
=======
                      [uu____15277]  in
>>>>>>> snap
=======
                      [uu____15336]  in
>>>>>>> nits
=======
              let uu____15344 =
                let uu____15345 = FStar_Syntax_Subst.compress signature  in
                uu____15345.FStar_Syntax_Syntax.n  in
              match uu____15344 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15349) when
                  (FStar_List.length bs) = (Prims.of_int (2)) ->
                  let uu____15378 = FStar_Syntax_Subst.open_binders bs  in
                  (match uu____15378 with
                   | (a,uu____15380)::(wp,uu____15382)::[] ->
                       FStar_All.pipe_right wp.FStar_Syntax_Syntax.sort
                         (FStar_Syntax_Subst.subst
                            [FStar_Syntax_Syntax.NT (a, a_tm)]))
              | uu____15411 ->
                  let uu____15412 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name signature
                     in
                  FStar_Errors.raise_error uu____15412 r
               in
            let uu____15418 =
              let uu____15431 =
                let uu____15433 = FStar_Range.string_of_range r  in
                FStar_Util.format2 "implicit for wp of %s at %s"
                  eff_name.FStar_Ident.str uu____15433
                 in
              new_implicit_var uu____15431 r env wp_sort  in
            match uu____15418 with
            | (wp_uvar,uu____15441,g_wp_uvar) ->
                let eff_c =
                  let uu____15456 =
                    let uu____15457 =
                      let uu____15468 =
                        FStar_All.pipe_right wp_uvar
                          FStar_Syntax_Syntax.as_arg
                         in
                      [uu____15468]  in
>>>>>>> snap
                    {
                      FStar_Syntax_Syntax.comp_univs = [u];
                      FStar_Syntax_Syntax.effect_name = eff_name;
                      FStar_Syntax_Syntax.result_typ = a_tm;
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                      FStar_Syntax_Syntax.effect_args = uu____15310;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____15309  in
                let uu____15354 =
                  let uu____15355 =
                    let uu____15362 =
                      let uu____15363 =
                        let uu____15378 =
                          let uu____15387 =
                            FStar_Syntax_Syntax.null_binder
                              FStar_Syntax_Syntax.t_unit
                             in
                          [uu____15387]  in
                        (uu____15378, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____15363  in
                    FStar_Syntax_Syntax.mk uu____15362  in
                  uu____15355 FStar_Pervasives_Native.None r  in
                (uu____15354, g_wp_uvar)
=======
                      FStar_Syntax_Syntax.effect_args = uu____15293;
=======
                      FStar_Syntax_Syntax.effect_args = uu____15294;
>>>>>>> cp
=======
                      FStar_Syntax_Syntax.effect_args = uu____15261;
>>>>>>> single tentative commit which could be reverted later
=======
                      FStar_Syntax_Syntax.effect_args = uu____15266;
>>>>>>> snap
=======
                      FStar_Syntax_Syntax.effect_args = uu____15325;
>>>>>>> nits
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____15324  in
                let uu____15369 =
                  let uu____15370 =
                    let uu____15377 =
                      let uu____15378 =
                        let uu____15393 =
                          let uu____15402 =
                            FStar_Syntax_Syntax.null_binder
                              FStar_Syntax_Syntax.t_unit
                             in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                          [uu____15370]  in
                        (uu____15361, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____15346  in
                    FStar_Syntax_Syntax.mk uu____15345  in
                  uu____15338 FStar_Pervasives_Native.None r  in
                (uu____15337, g_wp_uvar)
>>>>>>> snap
=======
                          [uu____15371]  in
                        (uu____15362, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____15347  in
                    FStar_Syntax_Syntax.mk uu____15346  in
                  uu____15339 FStar_Pervasives_Native.None r  in
                (uu____15338, g_wp_uvar)
>>>>>>> cp
=======
                          [uu____15338]  in
                        (uu____15329, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____15314  in
                    FStar_Syntax_Syntax.mk uu____15313  in
                  uu____15306 FStar_Pervasives_Native.None r  in
                (uu____15305, g_wp_uvar)
>>>>>>> single tentative commit which could be reverted later
=======
                          [uu____15343]  in
                        (uu____15334, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____15319  in
                    FStar_Syntax_Syntax.mk uu____15318  in
                  uu____15311 FStar_Pervasives_Native.None r  in
                (uu____15310, g_wp_uvar)
>>>>>>> snap
=======
                          [uu____15402]  in
                        (uu____15393, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____15378  in
                    FStar_Syntax_Syntax.mk uu____15377  in
                  uu____15370 FStar_Pervasives_Native.None r  in
                (uu____15369, g_wp_uvar)
>>>>>>> nits
=======
                      FStar_Syntax_Syntax.effect_args = uu____15457;
                      FStar_Syntax_Syntax.flags = []
                    }  in
                  FStar_Syntax_Syntax.mk_Comp uu____15456  in
                let uu____15501 =
                  let uu____15502 =
                    let uu____15509 =
                      let uu____15510 =
                        let uu____15525 =
                          let uu____15534 =
                            FStar_Syntax_Syntax.null_binder
                              FStar_Syntax_Syntax.t_unit
                             in
                          [uu____15534]  in
                        (uu____15525, eff_c)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____15510  in
                    FStar_Syntax_Syntax.mk uu____15509  in
                  uu____15502 FStar_Pervasives_Native.None r  in
                (uu____15501, g_wp_uvar)
>>>>>>> snap
  
let (fresh_layered_effect_repr :
=======
let (fresh_effect_repr :
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                  let uu____15466 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____15466 r  in
                let uu____15476 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____15476 with
                | (uu____15485,signature) ->
                    let uu____15487 =
                      let uu____15488 = FStar_Syntax_Subst.compress signature
                         in
                      uu____15488.FStar_Syntax_Syntax.n  in
                    (match uu____15487 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15496) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____15544 =
=======
                  let uu____15449 =
=======
                  let uu____15450 =
>>>>>>> cp
=======
                  let uu____15417 =
>>>>>>> single tentative commit which could be reverted later
=======
                  let uu____15422 =
>>>>>>> snap
=======
                  let uu____15481 =
>>>>>>> nits
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____15481 r  in
                let uu____15491 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____15491 with
                | (uu____15500,signature) ->
                    let uu____15502 =
                      let uu____15503 = FStar_Syntax_Subst.compress signature
                         in
                      uu____15503.FStar_Syntax_Syntax.n  in
                    (match uu____15502 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15511) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                              let uu____15527 =
>>>>>>> snap
=======
                              let uu____15528 =
>>>>>>> cp
=======
                              let uu____15495 =
>>>>>>> single tentative commit which could be reverted later
=======
                              let uu____15500 =
>>>>>>> snap
=======
                              let uu____15559 =
>>>>>>> nits
=======
                  let uu____15613 =
=======
                  let uu____15358 =
>>>>>>> snap
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____15358 r  in
                let uu____15368 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____15368 with
                | (uu____15377,signature) ->
                    let uu____15379 =
                      let uu____15380 = FStar_Syntax_Subst.compress signature
                         in
                      uu____15380.FStar_Syntax_Syntax.n  in
                    (match uu____15379 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15388) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
<<<<<<< HEAD
                              let uu____15691 =
>>>>>>> snap
=======
                              let uu____15436 =
>>>>>>> snap
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                     let uu____15559 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____15561 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____15559 eff_name.FStar_Ident.str
                                       uu____15561) r
                                 in
                              (match uu____15544 with
                               | (is,g) ->
                                   let repr =
                                     let uu____15575 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____15575
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____15584 =
                                     let uu____15585 =
                                       let uu____15590 =
=======
                                     let uu____15542 =
=======
                                     let uu____15543 =
>>>>>>> cp
=======
                                     let uu____15510 =
>>>>>>> single tentative commit which could be reverted later
=======
                                     let uu____15515 =
>>>>>>> snap
=======
                                     let uu____15574 =
>>>>>>> nits
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____15576 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____15574 eff_name.FStar_Ident.str
                                       uu____15576) r
                                 in
                              (match uu____15559 with
                               | (is,g) ->
                                   let repr =
                                     let uu____15590 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____15590
                                       FStar_Pervasives_Native.snd
                                      in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                   let uu____15567 =
                                     let uu____15568 =
                                       let uu____15573 =
>>>>>>> snap
=======
                                   let uu____15568 =
                                     let uu____15569 =
                                       let uu____15574 =
>>>>>>> cp
=======
                                   let uu____15535 =
                                     let uu____15536 =
                                       let uu____15541 =
>>>>>>> single tentative commit which could be reverted later
=======
                                   let uu____15540 =
                                     let uu____15541 =
                                       let uu____15546 =
>>>>>>> snap
=======
                                   let uu____15599 =
                                     let uu____15600 =
                                       let uu____15605 =
>>>>>>> nits
=======
                                     let uu____15706 =
=======
                                     let uu____15451 =
>>>>>>> snap
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____15453 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____15451 eff_name.FStar_Ident.str
                                       uu____15453) r
                                 in
                              (match uu____15436 with
                               | (is,g) ->
<<<<<<< HEAD
                                   let repr =
                                     let uu____15722 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts [u]
                                        in
                                     FStar_All.pipe_right uu____15722
                                       FStar_Pervasives_Native.snd
                                      in
                                   let uu____15731 =
                                     let uu____15732 =
                                       let uu____15737 =
>>>>>>> snap
                                         FStar_List.map
                                           FStar_Syntax_Syntax.as_arg (a_tm
                                           :: is)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                         uu____15590
                                        in
                                     uu____15585 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____15584, g))
                          | uu____15599 -> fail1 signature)
                     | uu____15600 -> fail1 signature)
=======
                                         uu____15573
=======
                                         uu____15574
>>>>>>> cp
=======
                                         uu____15541
>>>>>>> single tentative commit which could be reverted later
=======
                                         uu____15546
>>>>>>> snap
=======
                                         uu____15605
>>>>>>> nits
                                        in
                                     uu____15600 FStar_Pervasives_Native.None
                                       r
                                      in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                   (uu____15567, g))
                          | uu____15582 -> fail1 signature)
                     | uu____15583 -> fail1 signature)
>>>>>>> snap
=======
                                   (uu____15568, g))
                          | uu____15583 -> fail1 signature)
                     | uu____15584 -> fail1 signature)
>>>>>>> cp
=======
                                   (uu____15535, g))
                          | uu____15550 -> fail1 signature)
                     | uu____15551 -> fail1 signature)
>>>>>>> single tentative commit which could be reverted later
=======
                                   (uu____15540, g))
                          | uu____15555 -> fail1 signature)
                     | uu____15556 -> fail1 signature)
>>>>>>> snap
=======
                                   (uu____15599, g))
                          | uu____15614 -> fail1 signature)
                     | uu____15615 -> fail1 signature)
>>>>>>> nits
=======
                                         uu____15737
                                        in
                                     uu____15732 FStar_Pervasives_Native.None
                                       r
                                      in
                                   (uu____15731, g))
                          | uu____15746 -> fail1 signature)
                     | uu____15747 -> fail1 signature)
>>>>>>> snap
=======
                                   let uu____15466 =
                                     match repr_ts with
                                     | (uu____15467,{
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_unknown
                                                        ;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____15468;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____15469;_})
                                         ->
                                         let eff_c =
                                           let uu____15479 =
                                             let uu____15480 =
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
                                                 = uu____15480;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____15479
                                            in
                                         let uu____15499 =
                                           let uu____15506 =
                                             let uu____15507 =
                                               let uu____15522 =
                                                 let uu____15531 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____15531]  in
                                               (uu____15522, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____15507
                                              in
                                           FStar_Syntax_Syntax.mk uu____15506
                                            in
                                         uu____15499
                                           FStar_Pervasives_Native.None r
                                     | uu____15560 ->
                                         let repr =
                                           let uu____15562 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____15562
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____15571 =
                                           let uu____15576 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____15576
                                            in
                                         uu____15571
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____15466, g))
                          | uu____15585 -> fail1 signature)
                     | uu____15586 -> fail1 signature)
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
            let uu____15631 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____15631
=======
            let uu____15614 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____15614
>>>>>>> snap
=======
            let uu____15615 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____15615
>>>>>>> cp
=======
            let uu____15582 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____15582
>>>>>>> single tentative commit which could be reverted later
=======
            let uu____15587 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____15587
>>>>>>> snap
=======
            let uu____15646 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____15646
>>>>>>> nits
=======
            let uu____15778 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____15778
>>>>>>> snap
=======
            let uu____15617 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____15617
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
              let uu____15676 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____15676 with
              | (uu____15681,sig_tm) ->
                  let fail1 t =
                    let uu____15689 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____15689 r  in
                  let uu____15695 =
                    let uu____15696 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____15696.FStar_Syntax_Syntax.n  in
                  (match uu____15695 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15700) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____15723)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____15745 -> fail1 sig_tm)
                   | uu____15746 -> fail1 sig_tm)
=======
              let uu____15659 =
=======
              let uu____15660 =
>>>>>>> cp
=======
              let uu____15627 =
>>>>>>> single tentative commit which could be reverted later
=======
              let uu____15632 =
>>>>>>> snap
=======
              let uu____15691 =
>>>>>>> nits
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____15691 with
              | (uu____15696,sig_tm) ->
                  let fail1 t =
                    let uu____15704 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____15704 r  in
                  let uu____15710 =
                    let uu____15711 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____15711.FStar_Syntax_Syntax.n  in
                  (match uu____15710 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15715) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____15738)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                        | uu____15728 -> fail1 sig_tm)
                   | uu____15729 -> fail1 sig_tm)
>>>>>>> snap
=======
                        | uu____15729 -> fail1 sig_tm)
                   | uu____15730 -> fail1 sig_tm)
>>>>>>> cp
=======
                        | uu____15696 -> fail1 sig_tm)
                   | uu____15697 -> fail1 sig_tm)
>>>>>>> single tentative commit which could be reverted later
=======
                        | uu____15701 -> fail1 sig_tm)
                   | uu____15702 -> fail1 sig_tm)
>>>>>>> snap
=======
                        | uu____15760 -> fail1 sig_tm)
                   | uu____15761 -> fail1 sig_tm)
>>>>>>> nits
=======
              let uu____15823 =
=======
              let uu____15655 =
>>>>>>> snap
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____15655 with
              | (uu____15660,sig_tm) ->
                  let fail1 t =
                    let uu____15668 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____15668 r  in
                  let uu____15674 =
                    let uu____15675 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____15675.FStar_Syntax_Syntax.n  in
                  (match uu____15674 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____15679) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____15702)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
<<<<<<< HEAD
                        | uu____15892 -> fail1 sig_tm)
                   | uu____15893 -> fail1 sig_tm)
>>>>>>> snap
=======
                        | uu____15724 -> fail1 sig_tm)
                   | uu____15725 -> fail1 sig_tm)
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
          (let uu____15767 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____15767
           then
             let uu____15772 = FStar_Syntax_Print.comp_to_string c  in
             let uu____15774 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____15772 uu____15774
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____15804 =
               let uu____15805 =
                 let uu____15811 =
                   let uu____15813 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____15815 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____15813 uu____15815
                    in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15811)  in
               FStar_Errors.raise_error uu____15805 r  in
=======
          (let uu____15750 =
=======
          (let uu____15751 =
>>>>>>> cp
=======
          (let uu____15718 =
>>>>>>> single tentative commit which could be reverted later
=======
          (let uu____15723 =
>>>>>>> snap
=======
          (let uu____15782 =
>>>>>>> nits
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____15782
           then
             let uu____15787 = FStar_Syntax_Print.comp_to_string c  in
             let uu____15789 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____15787 uu____15789
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____15819 =
               let uu____15820 =
                 let uu____15826 =
                   let uu____15828 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____15830 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____15828 uu____15830
                    in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15794)  in
               FStar_Errors.raise_error uu____15788 r  in
>>>>>>> snap
=======
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15795)  in
               FStar_Errors.raise_error uu____15789 r  in
>>>>>>> cp
=======
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15762)  in
               FStar_Errors.raise_error uu____15756 r  in
>>>>>>> single tentative commit which could be reverted later
=======
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15767)  in
               FStar_Errors.raise_error uu____15761 r  in
>>>>>>> snap
=======
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15826)  in
               FStar_Errors.raise_error uu____15820 r  in
>>>>>>> nits
=======
          (let uu____15914 =
=======
          (let uu____15924 =
>>>>>>> snap
=======
          (let uu____15756 =
>>>>>>> snap
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____15756
           then
             let uu____15761 = FStar_Syntax_Print.comp_to_string c  in
             let uu____15763 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____15761 uu____15763
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let effect_args_from_repr repr is_layered =
             let err uu____15793 =
               let uu____15794 =
                 let uu____15800 =
                   let uu____15802 = FStar_Syntax_Print.term_to_string repr
                      in
                   let uu____15804 = FStar_Util.string_of_bool is_layered  in
                   FStar_Util.format2
                     "Could not get effect args from repr %s with is_layered %s"
                     uu____15802 uu____15804
                    in
<<<<<<< HEAD
<<<<<<< HEAD
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15958)  in
               FStar_Errors.raise_error uu____15952 r  in
>>>>>>> snap
=======
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15968)  in
               FStar_Errors.raise_error uu____15962 r  in
>>>>>>> snap
=======
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____15800)  in
               FStar_Errors.raise_error uu____15794 r  in
>>>>>>> snap
             let repr1 = FStar_Syntax_Subst.compress repr  in
             if is_layered
             then
               match repr1.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
               | FStar_Syntax_Syntax.Tm_app (uu____15827,uu____15828::is) ->
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____15896 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____15901,c1) ->
                    let uu____15923 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
                    FStar_All.pipe_right uu____15923
=======
               | FStar_Syntax_Syntax.Tm_app (uu____15810,uu____15811::is) ->
=======
               | FStar_Syntax_Syntax.Tm_app (uu____15811,uu____15812::is) ->
>>>>>>> cp
=======
               | FStar_Syntax_Syntax.Tm_app (uu____15778,uu____15779::is) ->
>>>>>>> single tentative commit which could be reverted later
=======
               | FStar_Syntax_Syntax.Tm_app (uu____15783,uu____15784::is) ->
>>>>>>> snap
=======
               | FStar_Syntax_Syntax.Tm_app (uu____15842,uu____15843::is) ->
>>>>>>> nits
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____15911 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____15916,c1) ->
                    let uu____15938 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                    FStar_All.pipe_right uu____15906
>>>>>>> snap
=======
                    FStar_All.pipe_right uu____15907
>>>>>>> cp
=======
                    FStar_All.pipe_right uu____15874
>>>>>>> single tentative commit which could be reverted later
=======
                    FStar_All.pipe_right uu____15879
>>>>>>> snap
=======
                    FStar_All.pipe_right uu____15938
>>>>>>> nits
=======
               | FStar_Syntax_Syntax.Tm_app (uu____15974,uu____15975::is) ->
=======
               | FStar_Syntax_Syntax.Tm_app (uu____15984,uu____15985::is) ->
>>>>>>> snap
=======
               | FStar_Syntax_Syntax.Tm_app (uu____15816,uu____15817::is) ->
>>>>>>> snap
                   FStar_All.pipe_right is
                     (FStar_List.map FStar_Pervasives_Native.fst)
               | uu____15885 -> err ()
             else
               (match repr1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (uu____15890,c1) ->
                    let uu____15912 =
                      FStar_All.pipe_right c1
                        FStar_Syntax_Util.comp_to_comp_typ
                       in
<<<<<<< HEAD
<<<<<<< HEAD
                    FStar_All.pipe_right uu____16070
>>>>>>> snap
=======
                    FStar_All.pipe_right uu____16080
>>>>>>> snap
=======
                    FStar_All.pipe_right uu____15912
>>>>>>> snap
                      (fun ct  ->
                         FStar_All.pipe_right
                           ct.FStar_Syntax_Syntax.effect_args
                           (FStar_List.map FStar_Pervasives_Native.fst))
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                | uu____15958 -> err ())
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____15960 =
             let uu____15971 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____15972 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____15971, (ct.FStar_Syntax_Syntax.result_typ), uu____15972)
              in
           match uu____15960 with
           | (u,a,c_is) ->
               let uu____16020 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____16020 with
                | (uu____16029,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____16040 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____16042 = FStar_Ident.string_of_lid tgt  in
                      let uu____16044 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____16040 uu____16042 s uu____16044
                       in
                    let uu____16047 =
                      let uu____16080 =
                        let uu____16081 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____16081.FStar_Syntax_Syntax.n  in
                      match uu____16080 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____16145 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____16145 with
                           | (a_b::bs1,c2) ->
                               let uu____16205 =
=======
                | uu____15941 -> err ())
=======
                | uu____15942 -> err ())
>>>>>>> cp
=======
                | uu____15909 -> err ())
>>>>>>> single tentative commit which could be reverted later
=======
                | uu____15914 -> err ())
>>>>>>> snap
=======
                | uu____15973 -> err ())
>>>>>>> nits
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____15975 =
             let uu____15986 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____15987 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____15986, (ct.FStar_Syntax_Syntax.result_typ), uu____15987)
              in
           match uu____15975 with
           | (u,a,c_is) ->
               let uu____16035 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____16035 with
                | (uu____16044,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____16055 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____16057 = FStar_Ident.string_of_lid tgt  in
                      let uu____16059 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____16055 uu____16057 s uu____16059
                       in
                    let uu____16062 =
                      let uu____16095 =
                        let uu____16096 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____16096.FStar_Syntax_Syntax.n  in
                      match uu____16095 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____16160 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____16160 with
                           | (a_b::bs1,c2) ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                               let uu____16188 =
>>>>>>> snap
=======
                               let uu____16189 =
>>>>>>> cp
=======
                               let uu____16156 =
>>>>>>> single tentative commit which could be reverted later
=======
                               let uu____16161 =
>>>>>>> snap
=======
                               let uu____16220 =
>>>>>>> nits
=======
                | uu____16105 -> err ())
=======
                | uu____16115 -> err ())
>>>>>>> snap
=======
                | uu____15947 -> err ())
>>>>>>> snap
              in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____15949 =
             let uu____15960 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____15961 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____15960, (ct.FStar_Syntax_Syntax.result_typ), uu____15961)
              in
           match uu____15949 with
           | (u,a,c_is) ->
               let uu____16009 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____16009 with
                | (uu____16018,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____16029 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____16031 = FStar_Ident.string_of_lid tgt  in
                      let uu____16033 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____16029 uu____16031 s uu____16033
                       in
                    let uu____16036 =
                      let uu____16069 =
                        let uu____16070 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____16070.FStar_Syntax_Syntax.n  in
                      match uu____16069 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____16134 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____16134 with
                           | (a_b::bs1,c2) ->
<<<<<<< HEAD
<<<<<<< HEAD
                               let uu____16352 =
>>>>>>> snap
=======
                               let uu____16362 =
>>>>>>> snap
=======
                               let uu____16194 =
>>>>>>> snap
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                               let uu____16267 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16205, uu____16267))
                      | uu____16294 ->
                          let uu____16295 =
                            let uu____16301 =
=======
                               let uu____16250 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16188, uu____16250))
                      | uu____16277 ->
                          let uu____16278 =
                            let uu____16284 =
>>>>>>> snap
=======
                               let uu____16251 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16189, uu____16251))
                      | uu____16278 ->
                          let uu____16279 =
                            let uu____16285 =
>>>>>>> cp
=======
                               let uu____16218 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16156, uu____16218))
                      | uu____16245 ->
                          let uu____16246 =
                            let uu____16252 =
>>>>>>> single tentative commit which could be reverted later
=======
                               let uu____16223 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16161, uu____16223))
                      | uu____16250 ->
                          let uu____16251 =
                            let uu____16257 =
>>>>>>> snap
=======
                               let uu____16282 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16220, uu____16282))
                      | uu____16309 ->
                          let uu____16310 =
                            let uu____16316 =
>>>>>>> nits
=======
                               let uu____16414 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16352, uu____16414))
                      | uu____16441 ->
                          let uu____16442 =
                            let uu____16448 =
>>>>>>> snap
=======
                               let uu____16424 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16362, uu____16424))
                      | uu____16451 ->
                          let uu____16452 =
                            let uu____16458 =
>>>>>>> snap
=======
                               let uu____16256 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____16194, uu____16256))
                      | uu____16283 ->
                          let uu____16284 =
                            let uu____16290 =
>>>>>>> snap
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                              uu____16301)
                             in
                          FStar_Errors.raise_error uu____16295 r
                       in
                    (match uu____16047 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____16419 =
                           let uu____16426 =
                             let uu____16427 =
                               let uu____16428 =
                                 let uu____16435 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____16435, a)  in
                               FStar_Syntax_Syntax.NT uu____16428  in
                             [uu____16427]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____16426
                             (fun b  ->
                                let uu____16452 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____16454 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____16456 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____16458 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____16452 uu____16454 uu____16456
                                  uu____16458) r
                            in
                         (match uu____16419 with
=======
                              uu____16284)
=======
                              uu____16285)
>>>>>>> cp
=======
                              uu____16252)
>>>>>>> single tentative commit which could be reverted later
=======
                              uu____16257)
>>>>>>> snap
=======
                              uu____16316)
>>>>>>> nits
                             in
                          FStar_Errors.raise_error uu____16310 r
                       in
                    (match uu____16062 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____16434 =
                           let uu____16441 =
                             let uu____16442 =
                               let uu____16443 =
                                 let uu____16450 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____16450, a)  in
                               FStar_Syntax_Syntax.NT uu____16443  in
                             [uu____16442]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____16441
                             (fun b  ->
                                let uu____16467 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____16469 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____16471 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____16473 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____16467 uu____16469 uu____16471
                                  uu____16473) r
                            in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                         (match uu____16402 with
>>>>>>> snap
                          | (rest_bs_uvars,g) ->
                              let substs =
                                FStar_List.map2
                                  (fun b  ->
                                     fun t  ->
<<<<<<< HEAD
                                       let uu____16495 =
                                         let uu____16502 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____16502, t)  in
                                       FStar_Syntax_Syntax.NT uu____16495)
=======
                                       let uu____16478 =
                                         let uu____16485 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____16485, t)  in
                                       FStar_Syntax_Syntax.NT uu____16478)
>>>>>>> snap
                                  (a_b :: rest_bs) (a :: rest_bs_uvars)
                                 in
                              let guard_f =
                                let f_sort =
<<<<<<< HEAD
                                  let uu____16521 =
=======
                                  let uu____16504 =
>>>>>>> snap
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                      (FStar_Syntax_Subst.subst substs)
                                     in
<<<<<<< HEAD
                                  FStar_All.pipe_right uu____16521
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____16527 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  effect_args_from_repr f_sort uu____16527
=======
                                  FStar_All.pipe_right uu____16504
                                    FStar_Syntax_Subst.compress
                                   in
                                let f_sort_is =
                                  let uu____16510 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  effect_args_from_repr f_sort uu____16510
>>>>>>> snap
                                   in
                                FStar_List.fold_left2
                                  (fun g1  ->
                                     fun i1  ->
                                       fun i2  ->
<<<<<<< HEAD
                                         let uu____16536 =
=======
                                         let uu____16519 =
>>>>>>> snap
                                           FStar_TypeChecker_Rel.teq env i1
                                             i2
                                            in
                                         FStar_TypeChecker_Env.conj_guard g1
<<<<<<< HEAD
                                           uu____16536)
=======
                                           uu____16519)
>>>>>>> snap
                                  FStar_TypeChecker_Env.trivial_guard c_is
                                  f_sort_is
                                 in
                              let is =
<<<<<<< HEAD
                                let uu____16540 =
=======
                                let uu____16523 =
>>>>>>> snap
                                  FStar_TypeChecker_Env.is_layered_effect env
                                    tgt
                                   in
                                effect_args_from_repr
                                  lift_ct.FStar_Syntax_Syntax.result_typ
<<<<<<< HEAD
                                  uu____16540
                                 in
                              let c1 =
                                let uu____16543 =
                                  let uu____16544 =
                                    let uu____16555 =
=======
                                  uu____16523
                                 in
                              let c1 =
                                let uu____16526 =
                                  let uu____16527 =
                                    let uu____16538 =
>>>>>>> snap
                                      FStar_All.pipe_right is
                                        (FStar_List.map
                                           (FStar_Syntax_Subst.subst substs))
                                       in
<<<<<<< HEAD
                                    FStar_All.pipe_right uu____16555
=======
                                    FStar_All.pipe_right uu____16538
>>>>>>> snap
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.as_arg)
                                     in
                                  {
                                    FStar_Syntax_Syntax.comp_univs =
                                      (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                    FStar_Syntax_Syntax.effect_name = tgt;
                                    FStar_Syntax_Syntax.result_typ = a;
                                    FStar_Syntax_Syntax.effect_args =
<<<<<<< HEAD
                                      uu____16544;
                                    FStar_Syntax_Syntax.flags =
                                      (ct.FStar_Syntax_Syntax.flags)
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____16543  in
                              ((let uu____16575 =
=======
                                      uu____16527;
                                    FStar_Syntax_Syntax.flags =
                                      (ct.FStar_Syntax_Syntax.flags)
                                  }  in
                                FStar_Syntax_Syntax.mk_Comp uu____16526  in
                              ((let uu____16558 =
>>>>>>> snap
=======
                         (match uu____16403 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____16456 =
>>>>>>> cp
=======
                         (match uu____16370 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____16423 =
>>>>>>> single tentative commit which could be reverted later
=======
                         (match uu____16375 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____16428 =
>>>>>>> snap
=======
                         (match uu____16434 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____16487 =
>>>>>>> nits
=======
                              uu____16448)
=======
                              uu____16458)
>>>>>>> snap
=======
                              uu____16290)
>>>>>>> snap
                             in
                          FStar_Errors.raise_error uu____16284 r
                       in
                    (match uu____16036 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____16408 =
                           let uu____16415 =
                             let uu____16416 =
                               let uu____16417 =
                                 let uu____16424 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____16424, a)  in
                               FStar_Syntax_Syntax.NT uu____16417  in
                             [uu____16416]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____16415
                             (fun b  ->
                                let uu____16441 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____16443 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____16445 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____16447 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____16441 uu____16443 uu____16445
                                  uu____16447) r
                            in
                         (match uu____16408 with
                          | (rest_bs_uvars,g) ->
<<<<<<< HEAD
<<<<<<< HEAD
                              ((let uu____16619 =
>>>>>>> snap
=======
                              ((let uu____16629 =
>>>>>>> snap
=======
                              ((let uu____16461 =
>>>>>>> snap
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                if uu____16575
                                then
                                  let uu____16580 =
                                    FStar_Syntax_Print.comp_to_string c1  in
                                  FStar_Util.print1 "} Lifted comp: %s\n"
                                    uu____16580
                                else ());
                               (let uu____16585 =
                                  FStar_TypeChecker_Env.conj_guard g guard_f
                                   in
                                (c1, uu____16585)))))))
=======
                                if uu____16558
=======
                                if uu____16456
>>>>>>> cp
=======
                                if uu____16423
>>>>>>> single tentative commit which could be reverted later
=======
                                if uu____16428
>>>>>>> snap
=======
                                if uu____16487
>>>>>>> nits
                                then
                                  let uu____16492 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____16501 =
                                             let uu____16503 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____16503
                                              in
                                           Prims.op_Hat s uu____16501) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____16492
=======
                                if uu____16619
=======
                                if uu____16629
>>>>>>> snap
=======
                                if uu____16461
>>>>>>> snap
                                then
                                  let uu____16466 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____16475 =
                                             let uu____16477 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____16477
                                              in
                                           Prims.op_Hat s uu____16475) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
<<<<<<< HEAD
<<<<<<< HEAD
                                    uu____16624
>>>>>>> snap
=======
                                    uu____16634
>>>>>>> snap
=======
                                    uu____16466
>>>>>>> snap
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                         let uu____16534 =
                                           let uu____16541 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____16541, t)  in
                                         FStar_Syntax_Syntax.NT uu____16534)
=======
                                         let uu____16666 =
                                           let uu____16673 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____16673, t)  in
                                         FStar_Syntax_Syntax.NT uu____16666)
>>>>>>> snap
=======
                                         let uu____16676 =
                                           let uu____16683 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____16683, t)  in
                                         FStar_Syntax_Syntax.NT uu____16676)
>>>>>>> snap
=======
                                         let uu____16508 =
                                           let uu____16515 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____16515, t)  in
                                         FStar_Syntax_Syntax.NT uu____16508)
>>>>>>> snap
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
<<<<<<< HEAD
                                (c1, uu____16568)))))))
>>>>>>> snap
=======
                                let guard_f =
                                  let f_sort =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                    let uu____16560 =
=======
                                    let uu____16692 =
>>>>>>> snap
=======
                                    let uu____16702 =
>>>>>>> snap
=======
                                    let uu____16534 =
>>>>>>> snap
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                    FStar_All.pipe_right uu____16560
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____16566 =
=======
                                    FStar_All.pipe_right uu____16692
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____16698 =
>>>>>>> snap
=======
                                    FStar_All.pipe_right uu____16702
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____16708 =
>>>>>>> snap
=======
                                    FStar_All.pipe_right uu____16534
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____16540 =
>>>>>>> snap
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                    effect_args_from_repr f_sort uu____16566
=======
                                    effect_args_from_repr f_sort uu____16698
>>>>>>> snap
=======
                                    effect_args_from_repr f_sort uu____16708
>>>>>>> snap
=======
                                    effect_args_from_repr f_sort uu____16540
>>>>>>> snap
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                           let uu____16575 =
=======
                                           let uu____16707 =
>>>>>>> snap
=======
                                           let uu____16717 =
>>>>>>> snap
=======
                                           let uu____16549 =
>>>>>>> snap
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                             g1 uu____16575)
=======
                                             g1 uu____16707)
>>>>>>> snap
=======
                                             g1 uu____16717)
>>>>>>> snap
=======
                                             g1 uu____16549)
>>>>>>> snap
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                  let uu____16579 =
=======
                                  let uu____16711 =
>>>>>>> snap
=======
                                  let uu____16721 =
>>>>>>> snap
=======
                                  let uu____16553 =
>>>>>>> snap
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                    uu____16579
                                   in
                                let c1 =
                                  let uu____16582 =
                                    let uu____16583 =
                                      let uu____16594 =
=======
                                    uu____16711
                                   in
                                let c1 =
                                  let uu____16714 =
                                    let uu____16715 =
                                      let uu____16726 =
>>>>>>> snap
=======
                                    uu____16721
                                   in
                                let c1 =
                                  let uu____16724 =
                                    let uu____16725 =
                                      let uu____16736 =
>>>>>>> snap
=======
                                    uu____16553
                                   in
                                let c1 =
                                  let uu____16556 =
                                    let uu____16557 =
                                      let uu____16568 =
>>>>>>> snap
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                      FStar_All.pipe_right uu____16594
=======
                                      FStar_All.pipe_right uu____16726
>>>>>>> snap
=======
                                      FStar_All.pipe_right uu____16736
>>>>>>> snap
=======
                                      FStar_All.pipe_right uu____16568
>>>>>>> snap
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                        uu____16583;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____16582  in
                                (let uu____16614 =
=======
                                        uu____16715;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____16714  in
                                (let uu____16746 =
>>>>>>> snap
=======
                                        uu____16725;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____16724  in
                                (let uu____16756 =
>>>>>>> snap
=======
                                        uu____16557;
                                      FStar_Syntax_Syntax.flags =
                                        (ct.FStar_Syntax_Syntax.flags)
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____16556  in
                                (let uu____16588 =
>>>>>>> snap
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                 if uu____16614
                                 then
                                   let uu____16619 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____16619
                                 else ());
                                (let uu____16624 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                 (c1, uu____16593))))))))
>>>>>>> cp
=======
                                 (c1, uu____16560))))))))
>>>>>>> single tentative commit which could be reverted later
=======
                                 (c1, uu____16565))))))))
>>>>>>> snap
=======
                                 (c1, uu____16624))))))))
>>>>>>> nits
=======
                                 if uu____16746
=======
                                 if uu____16756
>>>>>>> snap
=======
                                 if uu____16588
>>>>>>> snap
                                 then
                                   let uu____16593 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____16593
                                 else ());
                                (let uu____16598 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____16598))))))))
  
let (lift_tf_layered_effect_term :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun lift  ->
    fun lift_t  ->
      fun u  ->
        fun a  ->
          fun e  ->
            let uu____16625 =
              FStar_TypeChecker_Env.inst_tscheme_with lift [u]  in
            match uu____16625 with
            | (uu____16630,lift1) ->
                let rest_bs =
                  let uu____16641 =
                    let uu____16642 =
                      let uu____16645 =
                        FStar_All.pipe_right lift_t
                          FStar_Pervasives_Native.snd
                         in
                      FStar_All.pipe_right uu____16645
                        FStar_Syntax_Subst.compress
                       in
                    uu____16642.FStar_Syntax_Syntax.n  in
                  match uu____16641 with
                  | FStar_Syntax_Syntax.Tm_arrow
                      (uu____16668::bs,uu____16670) when
                      (FStar_List.length bs) >= Prims.int_one ->
                      let uu____16710 =
                        FStar_All.pipe_right bs
                          (FStar_List.splitAt
                             ((FStar_List.length bs) - Prims.int_one))
                         in
                      FStar_All.pipe_right uu____16710
                        FStar_Pervasives_Native.fst
                  | uu____16816 ->
                      let uu____16817 =
                        let uu____16823 =
                          let uu____16825 =
                            FStar_Syntax_Print.tscheme_to_string lift_t  in
                          FStar_Util.format1
                            "lift_t tscheme %s is not an arrow with enough binders"
                            uu____16825
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____16823)
                         in
                      FStar_Errors.raise_error uu____16817
                        (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
                   in
                let args =
                  let uu____16852 = FStar_Syntax_Syntax.as_arg a  in
                  let uu____16861 =
                    let uu____16872 =
                      FStar_All.pipe_right rest_bs
                        (FStar_List.map
                           (fun uu____16908  ->
                              FStar_Syntax_Syntax.as_arg
                                FStar_Syntax_Syntax.unit_const))
                       in
                    let uu____16915 =
                      let uu____16926 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____16926]  in
                    FStar_List.append uu____16872 uu____16915  in
                  uu____16852 :: uu____16861  in
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_app (lift1, args))
                  FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____16990 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____16990
      then
        let uu____16993 =
          let uu____17006 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____17006
           in
        let uu____17009 =
          let uu____17021 =
            let uu____17034 =
              FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                FStar_Util.must
               in
            let uu____17037 =
              FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                FStar_Util.must
               in
            lift_tf_layered_effect_term uu____17034 uu____17037  in
          FStar_Pervasives_Native.Some uu____17021  in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____16993;
          FStar_TypeChecker_Env.mlift_term = uu____17009
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____17072 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____17072 with
           | (uu____17081,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____17100 =
                 let uu____17101 =
                   let uu___2123_17102 = ct  in
                   let uu____17103 =
                     let uu____17114 =
                       let uu____17123 =
                         let uu____17124 =
                           let uu____17131 =
                             let uu____17132 =
                               let uu____17149 =
                                 let uu____17160 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____17160; wp]  in
                               (lift_t, uu____17149)  in
                             FStar_Syntax_Syntax.Tm_app uu____17132  in
                           FStar_Syntax_Syntax.mk uu____17131  in
                         uu____17124 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____17123
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____17114]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2123_17102.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2123_17102.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____17103;
                     FStar_Syntax_Syntax.flags =
                       (uu___2123_17102.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____17101  in
               (uu____17100, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____17260 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____17260 with
           | (uu____17267,lift_t) ->
               let uu____17269 =
                 let uu____17276 =
                   let uu____17277 =
                     let uu____17294 =
                       let uu____17305 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____17314 =
                         let uu____17325 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____17334 =
                           let uu____17345 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____17345]  in
                         uu____17325 :: uu____17334  in
                       uu____17305 :: uu____17314  in
                     (lift_t, uu____17294)  in
                   FStar_Syntax_Syntax.Tm_app uu____17277  in
                 FStar_Syntax_Syntax.mk uu____17276  in
               uu____17269 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____17398 =
           let uu____17411 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____17411 mk_mlift_wp  in
         let uu____17424 =
           FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____17398;
           FStar_TypeChecker_Env.mlift_term = uu____17424
         })
>>>>>>> snap
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____16604 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____16604 with
        | (uu____16609,t) ->
            let err n1 =
              let uu____16619 =
                let uu____16625 =
                  let uu____16627 = FStar_Ident.string_of_lid datacon  in
                  let uu____16629 = FStar_Util.string_of_int n1  in
                  let uu____16631 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____16627 uu____16629 uu____16631
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____16625)
                 in
              let uu____16635 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____16619 uu____16635  in
            let uu____16636 =
              let uu____16637 = FStar_Syntax_Subst.compress t  in
              uu____16637.FStar_Syntax_Syntax.n  in
            (match uu____16636 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16641) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____16696  ->
                           match uu____16696 with
                           | (uu____16704,q) ->
=======
        let uu____16587 = FStar_TypeChecker_Env.lookup_datacon env datacon
=======
        let uu____16612 = FStar_TypeChecker_Env.lookup_datacon env datacon
>>>>>>> cp
=======
        let uu____16579 = FStar_TypeChecker_Env.lookup_datacon env datacon
>>>>>>> single tentative commit which could be reverted later
=======
        let uu____16584 = FStar_TypeChecker_Env.lookup_datacon env datacon
>>>>>>> snap
=======
        let uu____16643 = FStar_TypeChecker_Env.lookup_datacon env datacon
>>>>>>> nits
           in
        match uu____16643 with
        | (uu____16648,t) ->
            let err n1 =
              let uu____16658 =
                let uu____16664 =
                  let uu____16666 = FStar_Ident.string_of_lid datacon  in
                  let uu____16668 = FStar_Util.string_of_int n1  in
                  let uu____16670 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____16666 uu____16668 uu____16670
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____16664)
                 in
              let uu____16674 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____16658 uu____16674  in
            let uu____16675 =
              let uu____16676 = FStar_Syntax_Subst.compress t  in
              uu____16676.FStar_Syntax_Syntax.n  in
            (match uu____16675 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____16680) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                        (fun uu____16679  ->
                           match uu____16679 with
                           | (uu____16687,q) ->
>>>>>>> snap
=======
                        (fun uu____16704  ->
                           match uu____16704 with
                           | (uu____16712,q) ->
>>>>>>> cp
=======
                        (fun uu____16671  ->
                           match uu____16671 with
                           | (uu____16679,q) ->
>>>>>>> single tentative commit which could be reverted later
=======
                        (fun uu____16676  ->
                           match uu____16676 with
                           | (uu____16684,q) ->
>>>>>>> snap
=======
                        (fun uu____16735  ->
                           match uu____16735 with
                           | (uu____16743,q) ->
>>>>>>> nits
=======
        let uu____17210 = FStar_TypeChecker_Env.lookup_datacon env datacon
=======
        let uu____17621 = FStar_TypeChecker_Env.lookup_datacon env datacon
>>>>>>> snap
=======
        let uu____17631 = FStar_TypeChecker_Env.lookup_datacon env datacon
>>>>>>> snap
=======
        let uu____17463 = FStar_TypeChecker_Env.lookup_datacon env datacon
>>>>>>> snap
           in
        match uu____17463 with
        | (uu____17468,t) ->
            let err n1 =
              let uu____17478 =
                let uu____17484 =
                  let uu____17486 = FStar_Ident.string_of_lid datacon  in
                  let uu____17488 = FStar_Util.string_of_int n1  in
                  let uu____17490 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____17486 uu____17488 uu____17490
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____17484)
                 in
              let uu____17494 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____17478 uu____17494  in
            let uu____17495 =
              let uu____17496 = FStar_Syntax_Subst.compress t  in
              uu____17496.FStar_Syntax_Syntax.n  in
            (match uu____17495 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____17500) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                        (fun uu____17302  ->
                           match uu____17302 with
                           | (uu____17310,q) ->
>>>>>>> snap
=======
                        (fun uu____17713  ->
                           match uu____17713 with
                           | (uu____17721,q) ->
>>>>>>> snap
=======
                        (fun uu____17723  ->
                           match uu____17723 with
                           | (uu____17731,q) ->
>>>>>>> snap
=======
                        (fun uu____17555  ->
                           match uu____17555 with
                           | (uu____17563,q) ->
>>>>>>> snap
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                | uu____16713 -> true)))
=======
                                | uu____16696 -> true)))
>>>>>>> snap
=======
                                | uu____16721 -> true)))
>>>>>>> cp
=======
                                | uu____16688 -> true)))
>>>>>>> single tentative commit which could be reverted later
=======
                                | uu____16693 -> true)))
>>>>>>> snap
=======
                                | uu____16752 -> true)))
>>>>>>> nits
=======
                                | uu____17319 -> true)))
>>>>>>> snap
=======
                                | uu____17730 -> true)))
>>>>>>> snap
=======
                                | uu____17740 -> true)))
>>>>>>> snap
=======
                                | uu____17572 -> true)))
>>>>>>> snap
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                    let uu____16745 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____16745
                      FStar_Pervasives_Native.fst)
             | uu____16756 -> err Prims.int_zero)
=======
                    let uu____16728 =
=======
                    let uu____16753 =
>>>>>>> cp
=======
                    let uu____16720 =
>>>>>>> single tentative commit which could be reverted later
=======
                    let uu____16725 =
>>>>>>> snap
=======
                    let uu____16784 =
>>>>>>> nits
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____16784
                      FStar_Pervasives_Native.fst)
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
             | uu____16739 -> err Prims.int_zero)
>>>>>>> snap
=======
             | uu____16764 -> err Prims.int_zero)
>>>>>>> cp
=======
             | uu____16731 -> err Prims.int_zero)
>>>>>>> single tentative commit which could be reverted later
=======
             | uu____16736 -> err Prims.int_zero)
>>>>>>> snap
=======
             | uu____16795 -> err Prims.int_zero)
>>>>>>> nits
=======
                    let uu____17351 =
=======
                    let uu____17762 =
>>>>>>> snap
=======
                    let uu____17772 =
>>>>>>> snap
=======
                    let uu____17604 =
>>>>>>> snap
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____17604
                      FStar_Pervasives_Native.fst)
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
             | uu____17362 -> err Prims.int_zero)
>>>>>>> snap
=======
             | uu____17773 -> err Prims.int_zero)
>>>>>>> snap
=======
             | uu____17783 -> err Prims.int_zero)
>>>>>>> snap
=======
             | uu____17615 -> err Prims.int_zero)
>>>>>>> snap
  