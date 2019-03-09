open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____60644 = FStar_TypeChecker_Env.get_range env  in
      let uu____60645 =
        FStar_TypeChecker_Err.failed_to_prove_specification errs  in
      FStar_Errors.log_issue uu____60644 uu____60645
  
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
        let uu____60706 =
          let uu____60708 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____60708  in
        if uu____60706
        then g
        else
          (let uu____60715 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____60767  ->
                     match uu____60767 with
                     | (uu____60774,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____60715 with
           | (solve_now,defer) ->
               ((let uu____60809 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____60809
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____60826  ->
                         match uu____60826 with
                         | (s,p) ->
                             let uu____60836 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____60836)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____60851  ->
                         match uu____60851 with
                         | (s,p) ->
                             let uu____60861 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____60861)
                      defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___631_60869 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___631_60869.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___631_60869.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___631_60869.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___634_60871 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___634_60871.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___634_60871.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___634_60871.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____60886 =
        let uu____60888 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____60888  in
      if uu____60886
      then
        let us =
          let uu____60893 =
            let uu____60897 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____60897
             in
          FStar_All.pipe_right uu____60893 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____60916 =
            let uu____60922 =
              let uu____60924 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____60924
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____60922)  in
          FStar_Errors.log_issue r uu____60916);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____60947  ->
      match uu____60947 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____60958;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____60960;
          FStar_Syntax_Syntax.lbpos = uu____60961;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____60996 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 e  in
               (match uu____60996 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____61034) ->
                          aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____61041)
                          -> FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____61096) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____61132 = FStar_Options.ml_ish ()  in
                                if uu____61132
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____61154 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____61154
                            then
                              let uu____61157 = FStar_Range.string_of_range r
                                 in
                              let uu____61159 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____61157 uu____61159
                            else ());
                           FStar_Util.Inl t2)
                      | uu____61164 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____61166 = aux e1  in
                      match uu____61166 with
                      | FStar_Util.Inr c ->
                          let uu____61172 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____61172
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____61177 =
                               let uu____61183 =
                                 let uu____61185 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____61185
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____61183)
                                in
                             FStar_Errors.raise_error uu____61177 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____61194 ->
               let uu____61195 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____61195 with
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
    let pat_as_arg uu____61259 =
      match uu____61259 with
      | (p,i) ->
          let uu____61279 = decorated_pattern_as_term p  in
          (match uu____61279 with
           | (vars,te) ->
               let uu____61302 =
                 let uu____61307 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____61307)  in
               (vars, uu____61302))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____61321 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____61321)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____61325 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____61325)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____61329 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____61329)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____61352 =
          let uu____61371 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____61371 FStar_List.unzip  in
        (match uu____61352 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____61509 =
               let uu____61510 =
                 let uu____61511 =
                   let uu____61528 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____61528, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____61511  in
               mk1 uu____61510  in
             (vars1, uu____61509))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____61567,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____61577,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____61591 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____61602 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp
       in
    FStar_All.pipe_right uu____61602 comp_univ_opt
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____61631)::[] -> wp
      | uu____61656 ->
          let uu____61667 =
            let uu____61669 =
              let uu____61671 =
                FStar_List.map
                  (fun uu____61685  ->
                     match uu____61685 with
                     | (x,uu____61694) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____61671 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____61669
             in
          failwith uu____61667
       in
    let uu____61705 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____61705, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____61722 = destruct_comp c  in
        match uu____61722 with
        | (u,uu____61730,wp) ->
            let uu____61732 =
              let uu____61743 =
                let uu____61752 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____61752  in
              [uu____61743]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____61732;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____61785 =
          let uu____61792 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____61793 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____61792 uu____61793  in
        match uu____61785 with | (m,uu____61795,uu____61796) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____61813 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____61813
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
        let uu____61860 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____61860 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____61897 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____61897 with
             | (a,kwp) ->
                 let uu____61928 = destruct_comp m1  in
                 let uu____61935 = destruct_comp m2  in
                 ((md, a, kwp), uu____61928, uu____61935))
  
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
            let uu____62020 =
              let uu____62021 =
                let uu____62032 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____62032]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____62021;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____62020
  
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
          let uu____62116 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____62116
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
      let uu____62132 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        uu____62132 lc.FStar_Syntax_Syntax.cflags
        (fun uu____62135  ->
           let uu____62136 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____62136)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____62144 =
      let uu____62145 = FStar_Syntax_Subst.compress t  in
      uu____62145.FStar_Syntax_Syntax.n  in
    match uu____62144 with
    | FStar_Syntax_Syntax.Tm_arrow uu____62149 -> true
    | uu____62165 -> false
  
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
              let uu____62235 =
                let uu____62237 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____62237  in
              if uu____62235
              then f
              else (let uu____62244 = reason1 ()  in label uu____62244 r f)
  
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
            let uu___828_62265 = g  in
            let uu____62266 =
              let uu____62267 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____62267  in
            {
              FStar_TypeChecker_Env.guard_f = uu____62266;
              FStar_TypeChecker_Env.deferred =
                (uu___828_62265.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___828_62265.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___828_62265.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____62288 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____62288
        then c
        else
          (let uu____62293 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____62293
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____62355 = FStar_Syntax_Syntax.mk_binder x
                            in
                         [uu____62355]  in
                       let us =
                         let uu____62377 =
                           let uu____62380 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____62380]  in
                         u_res :: uu____62377  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____62386 =
                         let uu____62391 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____62392 =
                           let uu____62393 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____62402 =
                             let uu____62413 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____62422 =
                               let uu____62433 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____62433]  in
                             uu____62413 :: uu____62422  in
                           uu____62393 :: uu____62402  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____62391
                           uu____62392
                          in
                       uu____62386 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____62475 = destruct_comp c1  in
              match uu____62475 with
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
          (fun uu____62511  ->
             let uu____62512 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____62512)
  
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
              ({ FStar_Syntax_Syntax.ppname = uu____62535;
                 FStar_Syntax_Syntax.index = uu____62536;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____62538;
                     FStar_Syntax_Syntax.vars = uu____62539;_};_},uu____62540)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____62548 -> c
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___585_62560  ->
            match uu___585_62560 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____62563 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit =
          let uu____62588 =
            let uu____62591 =
              FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____62591 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____62588
            (fun c  ->
               (let uu____62647 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____62647) &&
                 (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                    FStar_Syntax_Util.is_unit))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit))
               &&
               (let uu____62659 = FStar_Syntax_Util.head_and_args' e  in
                match uu____62659 with
                | (head1,uu____62676) ->
                    let uu____62697 =
                      let uu____62698 = FStar_Syntax_Util.un_uinst head1  in
                      uu____62698.FStar_Syntax_Syntax.n  in
                    (match uu____62697 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____62703 =
                           let uu____62705 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____62705
                            in
                         Prims.op_Negation uu____62703
                     | uu____62706 -> true)))
              &&
              (let uu____62709 = should_not_inline_lc lc  in
               Prims.op_Negation uu____62709)
  
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
            let uu____62737 =
              let uu____62739 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____62739  in
            if uu____62737
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____62746 = FStar_Syntax_Util.is_unit t  in
               if uu____62746
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
                    let uu____62755 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____62755
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____62760 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____62760 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____62770 =
                             let uu____62771 =
                               let uu____62776 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____62777 =
                                 let uu____62778 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____62787 =
                                   let uu____62798 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____62798]  in
                                 uu____62778 :: uu____62787  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____62776
                                 uu____62777
                                in
                             uu____62771 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env
                             uu____62770)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____62832 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____62832
           then
             let uu____62837 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____62839 = FStar_Syntax_Print.term_to_string v1  in
             let uu____62841 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____62837 uu____62839 uu____62841
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____62858 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___586_62864  ->
              match uu___586_62864 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____62867 -> false))
       in
    if uu____62858
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___587_62879  ->
              match uu___587_62879 with
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
        let uu____62899 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____62899
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____62905 = destruct_comp c1  in
           match uu____62905 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____62919 =
                   let uu____62924 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____62925 =
                     let uu____62926 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____62935 =
                       let uu____62946 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____62955 =
                         let uu____62966 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____62966]  in
                       uu____62946 :: uu____62955  in
                     uu____62926 :: uu____62935  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____62924 uu____62925  in
                 uu____62919 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____63007 = weaken_flags c1.FStar_Syntax_Syntax.flags
                  in
               mk_comp md u_res_t res_t wp1 uu____63007)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____63031 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____63033 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____63033
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____63039 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____63039 weaken
  
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
               let uu____63087 = destruct_comp c1  in
               match uu____63087 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____63101 =
                       let uu____63106 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____63107 =
                         let uu____63108 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____63117 =
                           let uu____63128 =
                             let uu____63137 =
                               let uu____63138 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____63138 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____63137
                              in
                           let uu____63147 =
                             let uu____63158 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____63158]  in
                           uu____63128 :: uu____63147  in
                         uu____63108 :: uu____63117  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____63106 uu____63107
                        in
                     uu____63101 FStar_Pervasives_Native.None
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
            let uu____63244 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____63244
            then (lc, g0)
            else
              (let flags =
                 let uu____63256 =
                   let uu____63264 =
                     FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
                   if uu____63264
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____63256 with
                 | (maybe_trivial_post,flags) ->
                     let uu____63294 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___588_63302  ->
                               match uu___588_63302 with
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
                               | uu____63305 -> []))
                        in
                     FStar_List.append flags uu____63294
                  in
               let strengthen uu____63311 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____63317 = FStar_TypeChecker_Env.guard_form g01
                       in
                    match uu____63317 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____63320 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____63320
                          then
                            let uu____63324 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____63326 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____63324 uu____63326
                          else ());
                         strengthen_comp env reason c f flags))
                  in
               let uu____63331 =
                 let uu____63332 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____63332
                   lc.FStar_Syntax_Syntax.res_typ flags strengthen
                  in
               (uu____63331,
                 (let uu___983_63334 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___983_63334.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___983_63334.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___983_63334.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___589_63343  ->
            match uu___589_63343 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____63347 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____63376 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____63376
          then e
          else
            (let uu____63383 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____63386 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____63386)
                in
             if uu____63383
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
          fun uu____63439  ->
            match uu____63439 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____63459 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____63459 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____63472 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____63472
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____63482 =
                         FStar_Syntax_Util.is_total_lcomp lc11  in
                       if uu____63482
                       then
                         let uu____63487 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____63487
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____63494 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____63494
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____63503 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____63503
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____63510 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____63510
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____63522 =
                  let uu____63523 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____63523
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
                       (fun uu____63540  ->
                          let uu____63541 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____63543 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____63548 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____63541 uu____63543 uu____63548);
                     (let aux uu____63566 =
                        let uu____63567 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____63567
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____63598 ->
                              let uu____63599 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____63599
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____63631 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____63631
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____63676 =
                        let uu____63677 =
                          let uu____63679 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____63679  in
                        if uu____63677
                        then
                          let uu____63693 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____63693
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____63716 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____63716))
                        else
                          (let uu____63731 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____63731
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___1049_63773 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1049_63773.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1049_63773.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____63774 =
                                 let uu____63780 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____63780, reason)  in
                               FStar_Util.Inl uu____63774  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____63816 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____63816
                                   (close1 x "c1 Tot")
                             | (uu____63830,FStar_Pervasives_Native.Some x)
                                 ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____63853,uu____63854) -> aux ()
                           else
                             (let uu____63869 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____63869
                              then
                                let uu____63882 =
                                  let uu____63888 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____63888, "both GTot")  in
                                FStar_Util.Inl uu____63882
                              else aux ()))
                         in
                      let uu____63899 = try_simplify ()  in
                      match uu____63899 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____63925  ->
                                let uu____63926 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____63926);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____63940  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____63962 = lift_and_destruct env c11 c21
                                 in
                              match uu____63962 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____64015 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____64015]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____64035 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____64035]
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
                                    let uu____64082 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____64091 =
                                      let uu____64102 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____64111 =
                                        let uu____64122 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____64131 =
                                          let uu____64142 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____64151 =
                                            let uu____64162 =
                                              let uu____64171 = mk_lam wp2
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____64171
                                               in
                                            [uu____64162]  in
                                          uu____64142 :: uu____64151  in
                                        uu____64122 :: uu____64131  in
                                      uu____64102 :: uu____64111  in
                                    uu____64082 :: uu____64091  in
                                  let wp =
                                    let uu____64223 =
                                      let uu____64228 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____64228 wp_args
                                       in
                                    uu____64223 FStar_Pervasives_Native.None
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
                              let uu____64251 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____64251 with
                              | (m,uu____64259,lift2) ->
                                  let c23 =
                                    let uu____64262 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____64262
                                     in
                                  let uu____64263 = destruct_comp c12  in
                                  (match uu____64263 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____64277 =
                                           let uu____64282 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____64283 =
                                             let uu____64284 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____64293 =
                                               let uu____64304 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____64304]  in
                                             uu____64284 :: uu____64293  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64282 uu____64283
                                            in
                                         uu____64277
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
                            let uu____64342 = destruct_comp c1_typ  in
                            match uu____64342 with
                            | (u_res_t1,res_t1,uu____64351) ->
                                let uu____64352 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____64352
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____64357 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____64357
                                   then
                                     (debug1
                                        (fun uu____64367  ->
                                           let uu____64368 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____64370 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____64368 uu____64370);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____64378 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____64381 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____64381)
                                         in
                                      if uu____64378
                                      then
                                        let e1' =
                                          let uu____64402 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____64402
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____64414  ->
                                              let uu____64415 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____64417 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____64415 uu____64417);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____64432  ->
                                              let uu____64433 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____64435 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____64433 uu____64435);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____64442 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____64442
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
      | uu____64460 -> g2
  
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
            (let uu____64484 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____64484)
           in
        let flags =
          if should_return1
          then
            let uu____64492 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____64492
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____64508 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____64512 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____64512
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____64518 =
              let uu____64520 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____64520  in
            (if uu____64518
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___1168_64527 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___1168_64527.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___1168_64527.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___1168_64527.FStar_Syntax_Syntax.effect_args);
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
               let uu____64540 =
                 let uu____64541 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____64541
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                 uu____64540
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____64544 =
               let uu____64545 =
                 let uu____64546 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____64546
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____64545  in
             FStar_Syntax_Util.comp_set_flags uu____64544 flags)
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
            fun uu____64584  ->
              match uu____64584 with
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
                    let uu____64596 =
                      ((let uu____64600 = is_pure_or_ghost_effect env eff1
                           in
                        Prims.op_Negation uu____64600) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____64596
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____64618 =
        let uu____64619 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____64619  in
      FStar_Syntax_Syntax.fvar uu____64618 FStar_Syntax_Syntax.delta_constant
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
               fun uu____64689  ->
                 match uu____64689 with
                 | (uu____64703,eff_label,uu____64705,uu____64706) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____64719 =
          let uu____64727 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____64765  ->
                    match uu____64765 with
                    | (uu____64780,uu____64781,flags,uu____64783) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___590_64800  ->
                                match uu___590_64800 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____64803 -> false))))
             in
          if uu____64727
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____64719 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____64836 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____64838 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____64838
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____64879 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____64880 =
                     let uu____64885 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____64886 =
                       let uu____64887 = FStar_Syntax_Syntax.as_arg res_t1
                          in
                       let uu____64896 =
                         let uu____64907 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____64916 =
                           let uu____64927 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____64936 =
                             let uu____64947 =
                               FStar_Syntax_Syntax.as_arg wp_e  in
                             [uu____64947]  in
                           uu____64927 :: uu____64936  in
                         uu____64907 :: uu____64916  in
                       uu____64887 :: uu____64896  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____64885 uu____64886
                      in
                   uu____64880 FStar_Pervasives_Native.None uu____64879  in
                 let default_case =
                   let post_k =
                     let uu____65000 =
                       let uu____65009 =
                         FStar_Syntax_Syntax.null_binder res_t  in
                       [uu____65009]  in
                     let uu____65028 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____65000 uu____65028  in
                   let kwp =
                     let uu____65034 =
                       let uu____65043 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____65043]  in
                     let uu____65062 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____65034 uu____65062  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____65069 =
                       let uu____65070 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____65070]  in
                     let uu____65089 =
                       let uu____65092 =
                         let uu____65099 =
                           FStar_TypeChecker_Env.get_range env  in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____65099
                          in
                       let uu____65100 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____65092 uu____65100  in
                     FStar_Syntax_Util.abs uu____65069 uu____65089
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
                   let uu____65124 =
                     should_not_inline_whole_match ||
                       (let uu____65127 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____65127)
                      in
                   if uu____65124 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____65166  ->
                        fun celse  ->
                          match uu____65166 with
                          | (g,eff_label,uu____65183,cthen) ->
                              let uu____65197 =
                                let uu____65222 =
                                  let uu____65223 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____65223
                                   in
                                lift_and_destruct env uu____65222 celse  in
                              (match uu____65197 with
                               | ((md,uu____65225,uu____65226),(uu____65227,uu____65228,wp_then),
                                  (uu____65230,uu____65231,wp_else)) ->
                                   let uu____65251 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____65251 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____65266::[] -> comp
                 | uu____65309 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____65328 = destruct_comp comp1  in
                     (match uu____65328 with
                      | (uu____65335,uu____65336,wp) ->
                          let wp1 =
                            let uu____65341 =
                              let uu____65346 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____65347 =
                                let uu____65348 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____65357 =
                                  let uu____65368 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____65368]  in
                                uu____65348 :: uu____65357  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____65346
                                uu____65347
                               in
                            uu____65341 FStar_Pervasives_Native.None
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
          let uu____65434 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____65434 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____65450 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____65456 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____65450 uu____65456
              else
                (let uu____65465 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____65471 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____65465 uu____65471)
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
          let uu____65496 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____65496
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____65499 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____65499
        then u_res
        else
          (let is_total =
             let uu____65506 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____65506
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____65517 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____65517 with
              | FStar_Pervasives_Native.None  ->
                  let uu____65520 =
                    let uu____65526 =
                      let uu____65528 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____65528
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____65526)
                     in
                  FStar_Errors.raise_error uu____65520
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
               let uu____65573 =
                 let uu____65574 = FStar_Syntax_Subst.compress t2  in
                 uu____65574.FStar_Syntax_Syntax.n  in
               match uu____65573 with
               | FStar_Syntax_Syntax.Tm_type uu____65578 -> true
               | uu____65580 -> false  in
             let uu____65582 =
               let uu____65583 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____65583.FStar_Syntax_Syntax.n  in
             match uu____65582 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____65591 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____65601 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____65601
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____65604 =
                     let uu____65605 =
                       let uu____65606 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____65606
                        in
                     (FStar_Pervasives_Native.None, uu____65605)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____65604
                    in
                 let e1 =
                   let uu____65612 =
                     let uu____65617 =
                       let uu____65618 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____65618]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____65617  in
                   uu____65612 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____65643 -> (e, lc))
  
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
          (let uu____65678 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____65678
           then
             let uu____65681 = FStar_Syntax_Print.term_to_string e  in
             let uu____65683 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____65685 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____65681 uu____65683 uu____65685
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____65695 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____65695 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____65720 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____65746 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____65746, false)
             else
               (let uu____65756 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____65756, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____65769) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____65781 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____65781
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___1324_65797 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___1324_65797.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___1324_65797.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___1324_65797.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____65804 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____65804 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____65816 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t  in
                      let uu____65827 =
                        let uu____65829 = FStar_Syntax_Util.eq_tm t res_t  in
                        uu____65829 = FStar_Syntax_Util.Equal  in
                      if uu____65827
                      then
                        ((let uu____65832 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____65832
                          then
                            let uu____65836 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____65838 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____65836 uu____65838
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
                           | FStar_Syntax_Syntax.Tm_refine uu____65849 ->
                               true
                           | uu____65857 -> false  in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t
                              in
                           let cret =
                             let uu____65862 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             return_value env (comp_univ_opt c) res_t
                               uu____65862
                              in
                           let lc1 =
                             let uu____65864 =
                               FStar_Syntax_Util.lcomp_of_comp c  in
                             let uu____65865 =
                               let uu____65866 =
                                 FStar_Syntax_Util.lcomp_of_comp cret  in
                               ((FStar_Pervasives_Native.Some x),
                                 uu____65866)
                                in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____65864
                               uu____65865
                              in
                           ((let uu____65870 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____65870
                             then
                               let uu____65874 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____65876 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               let uu____65878 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____65880 =
                                 FStar_Syntax_Print.lcomp_to_string lc1  in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____65874 uu____65876 uu____65878
                                 uu____65880
                             else ());
                            (let uu____65885 =
                               FStar_Syntax_Syntax.lcomp_comp lc1  in
                             set_result_typ1 uu____65885))
                         else
                           ((let uu____65889 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____65889
                             then
                               let uu____65893 =
                                 FStar_Syntax_Print.term_to_string res_t  in
                               let uu____65895 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____65893 uu____65895
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
                      let uu___1356_65903 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1356_65903.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1356_65903.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1356_65903.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____65909 =
                      let uu____65910 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____65910
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____65916 =
                           let uu____65917 = FStar_Syntax_Subst.compress f1
                              in
                           uu____65917.FStar_Syntax_Syntax.n  in
                         match uu____65916 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____65920,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____65922;
                                            FStar_Syntax_Syntax.vars =
                                              uu____65923;_},uu____65924)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1372_65950 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___1372_65950.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___1372_65950.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___1372_65950.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____65951 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____65954 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____65954
                               then
                                 let uu____65958 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____65960 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____65962 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____65964 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____65958 uu____65960 uu____65962
                                   uu____65964
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
                                   let uu____65977 =
                                     let uu____65982 =
                                       let uu____65983 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____65983]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____65982
                                      in
                                   uu____65977 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____66010 =
                                 let uu____66015 =
                                   FStar_All.pipe_left
                                     (fun _66036  ->
                                        FStar_Pervasives_Native.Some _66036)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____66037 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____66038 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____66039 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____66015
                                   uu____66037 e uu____66038 uu____66039
                                  in
                               match uu____66010 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___1388_66043 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___1388_66043.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___1388_66043.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____66045 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____66045
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____66050 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____66050
                                     then
                                       let uu____66054 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____66054
                                     else ());
                                    c2))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___591_66067  ->
                              match uu___591_66067 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____66070 -> []))
                       in
                    let lc1 =
                      let uu____66072 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____66072 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1402_66074 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1402_66074.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1402_66074.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1402_66074.FStar_TypeChecker_Env.implicits)
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
        let uu____66110 =
          let uu____66113 =
            let uu____66118 =
              let uu____66119 =
                let uu____66128 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____66128  in
              [uu____66119]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____66118  in
          uu____66113 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____66110  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____66151 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____66151
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____66170 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____66186 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____66203 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____66203
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____66219)::(ens,uu____66221)::uu____66222 ->
                    let uu____66265 =
                      let uu____66268 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____66268  in
                    let uu____66269 =
                      let uu____66270 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____66270  in
                    (uu____66265, uu____66269)
                | uu____66273 ->
                    let uu____66284 =
                      let uu____66290 =
                        let uu____66292 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____66292
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____66290)
                       in
                    FStar_Errors.raise_error uu____66284
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____66312)::uu____66313 ->
                    let uu____66340 =
                      let uu____66345 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____66345
                       in
                    (match uu____66340 with
                     | (us_r,uu____66377) ->
                         let uu____66378 =
                           let uu____66383 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____66383
                            in
                         (match uu____66378 with
                          | (us_e,uu____66415) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____66418 =
                                  let uu____66419 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____66419
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____66418
                                  us_r
                                 in
                              let as_ens =
                                let uu____66421 =
                                  let uu____66422 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____66422
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____66421
                                  us_e
                                 in
                              let req =
                                let uu____66426 =
                                  let uu____66431 =
                                    let uu____66432 =
                                      let uu____66443 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____66443]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____66432
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____66431
                                   in
                                uu____66426 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____66483 =
                                  let uu____66488 =
                                    let uu____66489 =
                                      let uu____66500 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____66500]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____66489
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____66488
                                   in
                                uu____66483 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____66537 =
                                let uu____66540 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____66540  in
                              let uu____66541 =
                                let uu____66542 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____66542  in
                              (uu____66537, uu____66541)))
                | uu____66545 -> failwith "Impossible"))
  
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
      (let uu____66579 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____66579
       then
         let uu____66584 = FStar_Syntax_Print.term_to_string tm  in
         let uu____66586 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____66584
           uu____66586
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
        (let uu____66640 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____66640
         then
           let uu____66645 = FStar_Syntax_Print.term_to_string tm  in
           let uu____66647 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____66645
             uu____66647
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____66658 =
      let uu____66660 =
        let uu____66661 = FStar_Syntax_Subst.compress t  in
        uu____66661.FStar_Syntax_Syntax.n  in
      match uu____66660 with
      | FStar_Syntax_Syntax.Tm_app uu____66665 -> false
      | uu____66683 -> true  in
    if uu____66658
    then t
    else
      (let uu____66688 = FStar_Syntax_Util.head_and_args t  in
       match uu____66688 with
       | (head1,args) ->
           let uu____66731 =
             let uu____66733 =
               let uu____66734 = FStar_Syntax_Subst.compress head1  in
               uu____66734.FStar_Syntax_Syntax.n  in
             match uu____66733 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____66739 -> false  in
           if uu____66731
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____66771 ->
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
          ((let uu____66818 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____66818
            then
              let uu____66821 = FStar_Syntax_Print.term_to_string e  in
              let uu____66823 = FStar_Syntax_Print.term_to_string t  in
              let uu____66825 =
                let uu____66827 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____66827
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____66821 uu____66823 uu____66825
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____66840 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____66840 with
              | (formals,uu____66856) ->
                  let n_implicits =
                    let uu____66878 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____66956  ->
                              match uu____66956 with
                              | (uu____66964,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____66971 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____66971 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____66878 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____67096 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____67096 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____67110 =
                      let uu____67116 =
                        let uu____67118 = FStar_Util.string_of_int n_expected
                           in
                        let uu____67120 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____67122 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____67118 uu____67120 uu____67122
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____67116)
                       in
                    let uu____67126 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____67110 uu____67126
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___592_67144 =
              match uu___592_67144 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____67187 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____67187 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _67318,uu____67305)
                           when _67318 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____67351,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____67353))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____67387 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____67387 with
                            | (v1,uu____67428,g) ->
                                ((let uu____67443 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____67443
                                  then
                                    let uu____67446 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____67446
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____67456 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____67456 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____67549 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____67549))))
                       | (uu____67576,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____67613 =
                             let uu____67626 =
                               let uu____67633 =
                                 let uu____67638 = FStar_Dyn.mkdyn env  in
                                 (uu____67638, tau)  in
                               FStar_Pervasives_Native.Some uu____67633  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____67626
                              in
                           (match uu____67613 with
                            | (v1,uu____67671,g) ->
                                ((let uu____67686 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____67686
                                  then
                                    let uu____67689 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____67689
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____67699 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____67699 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____67792 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____67792))))
                       | (uu____67819,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____67867 =
                       let uu____67894 = inst_n_binders t1  in
                       aux [] uu____67894 bs1  in
                     (match uu____67867 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____67966) -> (e, torig, guard)
                           | (uu____67997,[]) when
                               let uu____68028 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____68028 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____68030 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____68058 ->
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
            | uu____68071 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____68083 =
      let uu____68087 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____68087
        (FStar_List.map
           (fun u  ->
              let uu____68099 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____68099 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____68083 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____68127 = FStar_Util.set_is_empty x  in
      if uu____68127
      then []
      else
        (let s =
           let uu____68145 =
             let uu____68148 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____68148  in
           FStar_All.pipe_right uu____68145 FStar_Util.set_elements  in
         (let uu____68164 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____68164
          then
            let uu____68169 =
              let uu____68171 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____68171  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____68169
          else ());
         (let r =
            let uu____68180 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____68180  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____68219 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____68219
                     then
                       let uu____68224 =
                         let uu____68226 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____68226
                          in
                       let uu____68230 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____68232 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____68224 uu____68230 uu____68232
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
        let uu____68262 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____68262 FStar_Util.set_elements  in
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
        | ([],uu____68301) -> generalized_univ_names
        | (uu____68308,[]) -> explicit_univ_names
        | uu____68315 ->
            let uu____68324 =
              let uu____68330 =
                let uu____68332 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____68332
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____68330)
               in
            FStar_Errors.raise_error uu____68324 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____68354 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____68354
       then
         let uu____68359 = FStar_Syntax_Print.term_to_string t  in
         let uu____68361 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____68359 uu____68361
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____68370 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____68370
        then
          let uu____68375 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____68375
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____68384 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____68384
         then
           let uu____68389 = FStar_Syntax_Print.term_to_string t  in
           let uu____68391 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____68389 uu____68391
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
        let uu____68475 =
          let uu____68477 =
            FStar_Util.for_all
              (fun uu____68491  ->
                 match uu____68491 with
                 | (uu____68501,uu____68502,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____68477  in
        if uu____68475
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____68554 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____68554
              then
                let uu____68557 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____68557
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____68564 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____68564
               then
                 let uu____68567 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____68567
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____68585 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____68585 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____68619 =
             match uu____68619 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____68656 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____68656
                   then
                     let uu____68661 =
                       let uu____68663 =
                         let uu____68667 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____68667
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____68663
                         (FStar_String.concat ", ")
                        in
                     let uu____68715 =
                       let uu____68717 =
                         let uu____68721 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____68721
                           (FStar_List.map
                              (fun u  ->
                                 let uu____68734 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____68736 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____68734
                                   uu____68736))
                          in
                       FStar_All.pipe_right uu____68717
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____68661
                       uu____68715
                   else ());
                  (let univs2 =
                     let uu____68750 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____68762 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____68762) univs1
                       uu____68750
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____68769 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____68769
                    then
                      let uu____68774 =
                        let uu____68776 =
                          let uu____68780 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____68780
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____68776
                          (FStar_String.concat ", ")
                         in
                      let uu____68828 =
                        let uu____68830 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____68844 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____68846 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____68844
                                    uu____68846))
                           in
                        FStar_All.pipe_right uu____68830
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____68774 uu____68828
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____68867 =
             let uu____68884 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____68884  in
           match uu____68867 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____68974 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____68974
                 then ()
                 else
                   (let uu____68979 = lec_hd  in
                    match uu____68979 with
                    | (lb1,uu____68987,uu____68988) ->
                        let uu____68989 = lec2  in
                        (match uu____68989 with
                         | (lb2,uu____68997,uu____68998) ->
                             let msg =
                               let uu____69001 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____69003 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____69001 uu____69003
                                in
                             let uu____69006 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____69006))
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
                 let uu____69074 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____69074
                 then ()
                 else
                   (let uu____69079 = lec_hd  in
                    match uu____69079 with
                    | (lb1,uu____69087,uu____69088) ->
                        let uu____69089 = lec2  in
                        (match uu____69089 with
                         | (lb2,uu____69097,uu____69098) ->
                             let msg =
                               let uu____69101 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____69103 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____69101 uu____69103
                                in
                             let uu____69106 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____69106))
                  in
               let lecs1 =
                 let uu____69117 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____69170 = univs_and_uvars_of_lec this_lec  in
                        match uu____69170 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____69117 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____69275 = lec_hd  in
                   match uu____69275 with
                   | (lbname,e,c) ->
                       let uu____69285 =
                         let uu____69291 =
                           let uu____69293 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____69295 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____69297 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____69293 uu____69295 uu____69297
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____69291)
                          in
                       let uu____69301 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____69285 uu____69301
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____69320 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____69320 with
                         | FStar_Pervasives_Native.Some uu____69329 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____69337 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____69341 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____69341 with
                              | (bs,kres) ->
                                  ((let uu____69385 =
                                      let uu____69386 =
                                        let uu____69389 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____69389
                                         in
                                      uu____69386.FStar_Syntax_Syntax.n  in
                                    match uu____69385 with
                                    | FStar_Syntax_Syntax.Tm_type uu____69390
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____69394 =
                                          let uu____69396 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____69396  in
                                        if uu____69394
                                        then fail1 kres
                                        else ()
                                    | uu____69401 -> fail1 kres);
                                   (let a =
                                      let uu____69403 =
                                        let uu____69406 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _69409  ->
                                             FStar_Pervasives_Native.Some
                                               _69409) uu____69406
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____69403
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____69417 ->
                                          let uu____69426 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____69426
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
                      (fun uu____69529  ->
                         match uu____69529 with
                         | (lbname,e,c) ->
                             let uu____69575 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____69636 ->
                                   let uu____69649 = (e, c)  in
                                   (match uu____69649 with
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
                                                (fun uu____69689  ->
                                                   match uu____69689 with
                                                   | (x,uu____69695) ->
                                                       let uu____69696 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____69696)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____69714 =
                                                let uu____69716 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____69716
                                                 in
                                              if uu____69714
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
                                          let uu____69725 =
                                            let uu____69726 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____69726.FStar_Syntax_Syntax.n
                                             in
                                          match uu____69725 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____69751 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____69751 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____69762 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____69766 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____69766, gen_tvars))
                                in
                             (match uu____69575 with
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
        (let uu____69913 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____69913
         then
           let uu____69916 =
             let uu____69918 =
               FStar_List.map
                 (fun uu____69933  ->
                    match uu____69933 with
                    | (lb,uu____69942,uu____69943) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____69918 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____69916
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____69969  ->
                match uu____69969 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____69998 = gen env is_rec lecs  in
           match uu____69998 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____70097  ->
                       match uu____70097 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____70159 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____70159
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____70207  ->
                           match uu____70207 with
                           | (l,us,e,c,gvs) ->
                               let uu____70241 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____70243 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____70245 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____70247 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____70249 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____70241 uu____70243 uu____70245
                                 uu____70247 uu____70249))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____70294  ->
                match uu____70294 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____70338 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____70338, t, c, gvs)) univnames_lecs
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
              (let uu____70399 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____70399 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____70405 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _70408  -> FStar_Pervasives_Native.Some _70408)
                     uu____70405)
             in
          let is_var e1 =
            let uu____70416 =
              let uu____70417 = FStar_Syntax_Subst.compress e1  in
              uu____70417.FStar_Syntax_Syntax.n  in
            match uu____70416 with
            | FStar_Syntax_Syntax.Tm_name uu____70421 -> true
            | uu____70423 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1858_70444 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1858_70444.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1858_70444.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____70445 -> e2  in
          let env2 =
            let uu___1861_70447 = env1  in
            let uu____70448 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1861_70447.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1861_70447.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1861_70447.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1861_70447.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1861_70447.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1861_70447.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1861_70447.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1861_70447.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1861_70447.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1861_70447.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1861_70447.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1861_70447.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1861_70447.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1861_70447.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1861_70447.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1861_70447.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1861_70447.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____70448;
              FStar_TypeChecker_Env.is_iface =
                (uu___1861_70447.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1861_70447.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1861_70447.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1861_70447.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1861_70447.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1861_70447.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1861_70447.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1861_70447.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1861_70447.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1861_70447.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1861_70447.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1861_70447.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1861_70447.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1861_70447.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1861_70447.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1861_70447.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1861_70447.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1861_70447.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1861_70447.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1861_70447.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1861_70447.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1861_70447.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1861_70447.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1861_70447.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1861_70447.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____70450 = check1 env2 t1 t2  in
          match uu____70450 with
          | FStar_Pervasives_Native.None  ->
              let uu____70457 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____70463 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____70457 uu____70463
          | FStar_Pervasives_Native.Some g ->
              ((let uu____70470 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70470
                then
                  let uu____70475 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____70475
                else ());
               (let uu____70481 = decorate e t2  in (uu____70481, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____70509 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____70509
         then
           let uu____70512 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____70512
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____70526 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____70526
         then
           let uu____70534 = discharge g1  in
           let uu____70536 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____70534, uu____70536)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____70545 =
                let uu____70546 =
                  let uu____70547 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____70547
                    FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____70546
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____70545
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____70549 = destruct_comp c1  in
            match uu____70549 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____70567 = FStar_TypeChecker_Env.get_range env  in
                  let uu____70568 =
                    let uu____70573 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____70574 =
                      let uu____70575 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____70584 =
                        let uu____70595 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____70595]  in
                      uu____70575 :: uu____70584  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____70573 uu____70574  in
                  uu____70568 FStar_Pervasives_Native.None uu____70567  in
                ((let uu____70629 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____70629
                  then
                    let uu____70634 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____70634
                  else ());
                 (let g2 =
                    let uu____70640 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____70640  in
                  let uu____70641 = discharge g2  in
                  let uu____70643 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____70641, uu____70643)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___593_70677 =
        match uu___593_70677 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____70687)::[] -> f fst1
        | uu____70712 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____70724 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____70724
          (fun _70725  -> FStar_TypeChecker_Common.NonTrivial _70725)
         in
      let op_or_e e =
        let uu____70736 =
          let uu____70737 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____70737  in
        FStar_All.pipe_right uu____70736
          (fun _70740  -> FStar_TypeChecker_Common.NonTrivial _70740)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _70747  -> FStar_TypeChecker_Common.NonTrivial _70747)
         in
      let op_or_t t =
        let uu____70758 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____70758
          (fun _70761  -> FStar_TypeChecker_Common.NonTrivial _70761)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _70768  -> FStar_TypeChecker_Common.NonTrivial _70768)
         in
      let short_op_ite uu___594_70774 =
        match uu___594_70774 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____70784)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____70811)::[] ->
            let uu____70852 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____70852
              (fun _70853  -> FStar_TypeChecker_Common.NonTrivial _70853)
        | uu____70854 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____70866 =
          let uu____70874 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____70874)  in
        let uu____70882 =
          let uu____70892 =
            let uu____70900 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____70900)  in
          let uu____70908 =
            let uu____70918 =
              let uu____70926 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____70926)  in
            let uu____70934 =
              let uu____70944 =
                let uu____70952 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____70952)  in
              let uu____70960 =
                let uu____70970 =
                  let uu____70978 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____70978)  in
                [uu____70970; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____70944 :: uu____70960  in
            uu____70918 :: uu____70934  in
          uu____70892 :: uu____70908  in
        uu____70866 :: uu____70882  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____71040 =
            FStar_Util.find_map table
              (fun uu____71055  ->
                 match uu____71055 with
                 | (x,mk1) ->
                     let uu____71072 = FStar_Ident.lid_equals x lid  in
                     if uu____71072
                     then
                       let uu____71077 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____71077
                     else FStar_Pervasives_Native.None)
             in
          (match uu____71040 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____71081 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____71089 =
      let uu____71090 = FStar_Syntax_Util.un_uinst l  in
      uu____71090.FStar_Syntax_Syntax.n  in
    match uu____71089 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____71095 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____71131)::uu____71132 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____71151 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____71160,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____71161))::uu____71162 -> bs
      | uu____71180 ->
          let uu____71181 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____71181 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____71185 =
                 let uu____71186 = FStar_Syntax_Subst.compress t  in
                 uu____71186.FStar_Syntax_Syntax.n  in
               (match uu____71185 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____71190) ->
                    let uu____71211 =
                      FStar_Util.prefix_until
                        (fun uu___595_71251  ->
                           match uu___595_71251 with
                           | (uu____71259,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____71260)) ->
                               false
                           | uu____71265 -> true) bs'
                       in
                    (match uu____71211 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____71301,uu____71302) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____71374,uu____71375) ->
                         let uu____71448 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____71468  ->
                                   match uu____71468 with
                                   | (x,uu____71477) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____71448
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____71526  ->
                                     match uu____71526 with
                                     | (x,i) ->
                                         let uu____71545 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____71545, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____71556 -> bs))
  
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
            let uu____71585 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____71585
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
          let uu____71616 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____71616
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
        (let uu____71659 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____71659
         then
           ((let uu____71664 = FStar_Ident.text_of_lid lident  in
             d uu____71664);
            (let uu____71666 = FStar_Ident.text_of_lid lident  in
             let uu____71668 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____71666 uu____71668))
         else ());
        (let fv =
           let uu____71674 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____71674
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
         let uu____71686 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2019_71688 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2019_71688.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2019_71688.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2019_71688.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2019_71688.FStar_Syntax_Syntax.sigattrs)
           }), uu____71686))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___596_71706 =
        match uu___596_71706 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____71709 -> false  in
      let reducibility uu___597_71717 =
        match uu___597_71717 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____71724 -> false  in
      let assumption uu___598_71732 =
        match uu___598_71732 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____71736 -> false  in
      let reification uu___599_71744 =
        match uu___599_71744 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____71747 -> true
        | uu____71749 -> false  in
      let inferred uu___600_71757 =
        match uu___600_71757 with
        | FStar_Syntax_Syntax.Discriminator uu____71759 -> true
        | FStar_Syntax_Syntax.Projector uu____71761 -> true
        | FStar_Syntax_Syntax.RecordType uu____71767 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____71777 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____71790 -> false  in
      let has_eq uu___601_71798 =
        match uu___601_71798 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____71802 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____71881 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____71888 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____71899 =
        let uu____71901 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___602_71907  ->
                  match uu___602_71907 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____71910 -> false))
           in
        FStar_All.pipe_right uu____71901 Prims.op_Negation  in
      if uu____71899
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____71931 =
            let uu____71937 =
              let uu____71939 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____71939 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____71937)  in
          FStar_Errors.raise_error uu____71931 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____71957 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____71965 =
            let uu____71967 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____71967  in
          if uu____71965 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____71977),uu____71978) ->
              ((let uu____71990 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____71990
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____71999 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____71999
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____72010 ->
              let uu____72019 =
                let uu____72021 =
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
                Prims.op_Negation uu____72021  in
              if uu____72019 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____72031 ->
              let uu____72038 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____72038 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____72046 ->
              let uu____72053 =
                let uu____72055 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____72055  in
              if uu____72053 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____72065 ->
              let uu____72066 =
                let uu____72068 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____72068  in
              if uu____72066 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____72078 ->
              let uu____72079 =
                let uu____72081 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____72081  in
              if uu____72079 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____72091 ->
              let uu____72104 =
                let uu____72106 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____72106  in
              if uu____72104 then err'1 () else ()
          | uu____72116 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____72139 =
          let uu____72144 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____72144
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____72139
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____72163 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____72163
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____72181 =
                          let uu____72182 = FStar_Syntax_Subst.compress t1
                             in
                          uu____72182.FStar_Syntax_Syntax.n  in
                        match uu____72181 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____72188 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____72214 =
          let uu____72215 = FStar_Syntax_Subst.compress t1  in
          uu____72215.FStar_Syntax_Syntax.n  in
        match uu____72214 with
        | FStar_Syntax_Syntax.Tm_type uu____72219 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____72222 ->
            let uu____72237 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____72237 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____72270 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____72270
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____72276;
               FStar_Syntax_Syntax.index = uu____72277;
               FStar_Syntax_Syntax.sort = t2;_},uu____72279)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72288,uu____72289) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____72331::[]) ->
            let uu____72370 =
              let uu____72371 = FStar_Syntax_Util.un_uinst head1  in
              uu____72371.FStar_Syntax_Syntax.n  in
            (match uu____72370 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____72376 -> false)
        | uu____72378 -> false
      
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
        (let uu____72388 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____72388
         then
           let uu____72393 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____72393
         else ());
        res
       in aux g t
  