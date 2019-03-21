open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____60663 = FStar_TypeChecker_Env.get_range env  in
      let uu____60664 =
        FStar_TypeChecker_Err.failed_to_prove_specification errs  in
      FStar_Errors.log_issue uu____60663 uu____60664
  
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
        let uu____60725 =
          let uu____60727 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____60727  in
        if uu____60725
        then g
        else
          (let uu____60734 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____60786  ->
                     match uu____60786 with
                     | (uu____60793,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____60734 with
           | (solve_now,defer) ->
               ((let uu____60828 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____60828
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____60845  ->
                         match uu____60845 with
                         | (s,p) ->
                             let uu____60855 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____60855)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____60870  ->
                         match uu____60870 with
                         | (s,p) ->
                             let uu____60880 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____60880)
                      defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___631_60888 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___631_60888.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___631_60888.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___631_60888.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___634_60890 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___634_60890.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___634_60890.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___634_60890.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____60905 =
        let uu____60907 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____60907  in
      if uu____60905
      then
        let us =
          let uu____60912 =
            let uu____60916 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____60916
             in
          FStar_All.pipe_right uu____60912 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____60935 =
            let uu____60941 =
              let uu____60943 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____60943
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____60941)  in
          FStar_Errors.log_issue r uu____60935);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____60966  ->
      match uu____60966 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____60977;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____60979;
          FStar_Syntax_Syntax.lbpos = uu____60980;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____61015 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 e  in
               (match uu____61015 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____61053) ->
                          aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____61060)
                          -> FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____61115) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____61151 = FStar_Options.ml_ish ()  in
                                if uu____61151
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____61173 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____61173
                            then
                              let uu____61176 = FStar_Range.string_of_range r
                                 in
                              let uu____61178 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____61176 uu____61178
                            else ());
                           FStar_Util.Inl t2)
                      | uu____61183 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____61185 = aux e1  in
                      match uu____61185 with
                      | FStar_Util.Inr c ->
                          let uu____61191 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____61191
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____61196 =
                               let uu____61202 =
                                 let uu____61204 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____61204
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____61202)
                                in
                             FStar_Errors.raise_error uu____61196 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____61213 ->
               let uu____61214 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____61214 with
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
    let pat_as_arg uu____61278 =
      match uu____61278 with
      | (p,i) ->
          let uu____61298 = decorated_pattern_as_term p  in
          (match uu____61298 with
           | (vars,te) ->
               let uu____61321 =
                 let uu____61326 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____61326)  in
               (vars, uu____61321))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____61340 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____61340)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____61344 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____61344)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____61348 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____61348)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____61371 =
          let uu____61390 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____61390 FStar_List.unzip  in
        (match uu____61371 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____61528 =
               let uu____61529 =
                 let uu____61530 =
                   let uu____61547 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____61547, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____61530  in
               mk1 uu____61529  in
             (vars1, uu____61528))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____61586,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____61596,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____61610 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun lc  ->
    let uu____61621 = FStar_All.pipe_right lc FStar_Syntax_Syntax.lcomp_comp
       in
    FStar_All.pipe_right uu____61621 comp_univ_opt
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____61650)::[] -> wp
      | uu____61675 ->
          let uu____61686 =
            let uu____61688 =
              let uu____61690 =
                FStar_List.map
                  (fun uu____61704  ->
                     match uu____61704 with
                     | (x,uu____61713) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____61690 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____61688
             in
          failwith uu____61686
       in
    let uu____61724 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____61724, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____61741 = destruct_comp c  in
        match uu____61741 with
        | (u,uu____61749,wp) ->
            let uu____61751 =
              let uu____61762 =
                let uu____61771 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____61771  in
              [uu____61762]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____61751;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____61804 =
          let uu____61811 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____61812 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____61811 uu____61812  in
        match uu____61804 with | (m,uu____61814,uu____61815) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____61832 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____61832
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
        let uu____61879 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____61879 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____61916 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____61916 with
             | (a,kwp) ->
                 let uu____61947 = destruct_comp m1  in
                 let uu____61954 = destruct_comp m2  in
                 ((md, a, kwp), uu____61947, uu____61954))
  
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
            let uu____62039 =
              let uu____62040 =
                let uu____62051 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____62051]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____62040;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____62039
  
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
          let uu____62135 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____62135
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
      let uu____62151 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        uu____62151 lc.FStar_Syntax_Syntax.cflags
        (fun uu____62154  ->
           let uu____62155 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____62155)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____62163 =
      let uu____62164 = FStar_Syntax_Subst.compress t  in
      uu____62164.FStar_Syntax_Syntax.n  in
    match uu____62163 with
    | FStar_Syntax_Syntax.Tm_arrow uu____62168 -> true
    | uu____62184 -> false
  
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
              let uu____62254 =
                let uu____62256 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____62256  in
              if uu____62254
              then f
              else (let uu____62263 = reason1 ()  in label uu____62263 r f)
  
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
            let uu___828_62284 = g  in
            let uu____62285 =
              let uu____62286 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____62286  in
            {
              FStar_TypeChecker_Env.guard_f = uu____62285;
              FStar_TypeChecker_Env.deferred =
                (uu___828_62284.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___828_62284.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___828_62284.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____62307 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____62307
        then c
        else
          (let uu____62312 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____62312
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____62374 = FStar_Syntax_Syntax.mk_binder x
                            in
                         [uu____62374]  in
                       let us =
                         let uu____62396 =
                           let uu____62399 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____62399]  in
                         u_res :: uu____62396  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____62405 =
                         let uu____62410 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____62411 =
                           let uu____62412 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____62421 =
                             let uu____62432 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____62441 =
                               let uu____62452 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____62452]  in
                             uu____62432 :: uu____62441  in
                           uu____62412 :: uu____62421  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____62410
                           uu____62411
                          in
                       uu____62405 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____62494 = destruct_comp c1  in
              match uu____62494 with
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
          (fun uu____62530  ->
             let uu____62531 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____62531)
  
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
              ({ FStar_Syntax_Syntax.ppname = uu____62554;
                 FStar_Syntax_Syntax.index = uu____62555;
                 FStar_Syntax_Syntax.sort =
                   { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                     FStar_Syntax_Syntax.pos = uu____62557;
                     FStar_Syntax_Syntax.vars = uu____62558;_};_},uu____62559)
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              close_comp env [x] c
          | uu____62567 -> c
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___585_62579  ->
            match uu___585_62579 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____62582 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit =
          let uu____62607 =
            let uu____62610 =
              FStar_All.pipe_right lc.FStar_Syntax_Syntax.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____62610 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____62607
            (fun c  ->
               (let uu____62666 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____62666) &&
                 (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                    FStar_Syntax_Util.is_unit))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit))
               &&
               (let uu____62678 = FStar_Syntax_Util.head_and_args' e  in
                match uu____62678 with
                | (head1,uu____62695) ->
                    let uu____62716 =
                      let uu____62717 = FStar_Syntax_Util.un_uinst head1  in
                      uu____62717.FStar_Syntax_Syntax.n  in
                    (match uu____62716 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____62722 =
                           let uu____62724 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____62724
                            in
                         Prims.op_Negation uu____62722
                     | uu____62725 -> true)))
              &&
              (let uu____62728 = should_not_inline_lc lc  in
               Prims.op_Negation uu____62728)
  
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
            let uu____62756 =
              let uu____62758 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____62758  in
            if uu____62756
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____62765 = FStar_Syntax_Util.is_unit t  in
               if uu____62765
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
                    let uu____62774 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____62774
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____62779 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____62779 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____62789 =
                             let uu____62790 =
                               let uu____62795 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____62796 =
                                 let uu____62797 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____62806 =
                                   let uu____62817 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____62817]  in
                                 uu____62797 :: uu____62806  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____62795
                                 uu____62796
                                in
                             uu____62790 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.NoFullNorm] env
                             uu____62789)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____62851 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____62851
           then
             let uu____62856 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____62858 = FStar_Syntax_Print.term_to_string v1  in
             let uu____62860 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____62856 uu____62858 uu____62860
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____62877 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___586_62883  ->
              match uu___586_62883 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____62886 -> false))
       in
    if uu____62877
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___587_62898  ->
              match uu___587_62898 with
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
        let uu____62918 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____62918
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____62924 = destruct_comp c1  in
           match uu____62924 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____62938 =
                   let uu____62943 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____62944 =
                     let uu____62945 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____62954 =
                       let uu____62965 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____62974 =
                         let uu____62985 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____62985]  in
                       uu____62965 :: uu____62974  in
                     uu____62945 :: uu____62954  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____62943 uu____62944  in
                 uu____62938 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____63026 = weaken_flags c1.FStar_Syntax_Syntax.flags
                  in
               mk_comp md u_res_t res_t wp1 uu____63026)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____63050 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____63052 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____63052
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____63058 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____63058 weaken
  
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
               let uu____63106 = destruct_comp c1  in
               match uu____63106 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____63120 =
                       let uu____63125 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____63126 =
                         let uu____63127 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____63136 =
                           let uu____63147 =
                             let uu____63156 =
                               let uu____63157 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____63157 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____63156
                              in
                           let uu____63166 =
                             let uu____63177 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____63177]  in
                           uu____63147 :: uu____63166  in
                         uu____63127 :: uu____63136  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____63125 uu____63126
                        in
                     uu____63120 FStar_Pervasives_Native.None
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
            let uu____63263 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____63263
            then (lc, g0)
            else
              (let flags =
                 let uu____63275 =
                   let uu____63283 =
                     FStar_Syntax_Util.is_tot_or_gtot_lcomp lc  in
                   if uu____63283
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____63275 with
                 | (maybe_trivial_post,flags) ->
                     let uu____63313 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___588_63321  ->
                               match uu___588_63321 with
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
                               | uu____63324 -> []))
                        in
                     FStar_List.append flags uu____63313
                  in
               let strengthen uu____63330 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____63336 = FStar_TypeChecker_Env.guard_form g01
                       in
                    match uu____63336 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____63339 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____63339
                          then
                            let uu____63343 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debugging_only
                               in
                            let uu____63345 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____63343 uu____63345
                          else ());
                         strengthen_comp env reason c f flags))
                  in
               let uu____63350 =
                 let uu____63351 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____63351
                   lc.FStar_Syntax_Syntax.res_typ flags strengthen
                  in
               (uu____63350,
                 (let uu___983_63353 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___983_63353.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___983_63353.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___983_63353.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___589_63362  ->
            match uu___589_63362 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____63366 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____63395 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____63395
          then e
          else
            (let uu____63402 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____63405 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____63405)
                in
             if uu____63402
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
          fun uu____63458  ->
            match uu____63458 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____63478 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____63478 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____63491 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____63491
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____63501 =
                         FStar_Syntax_Util.is_total_lcomp lc11  in
                       if uu____63501
                       then
                         let uu____63506 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____63506
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____63513 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____63513
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____63522 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____63522
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____63529 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____63529
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____63541 =
                  let uu____63542 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____63542
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
                       (fun uu____63559  ->
                          let uu____63560 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____63562 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____63567 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____63560 uu____63562 uu____63567);
                     (let aux uu____63585 =
                        let uu____63586 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____63586
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____63617 ->
                              let uu____63618 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____63618
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____63650 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____63650
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let try_simplify uu____63695 =
                        let uu____63696 =
                          let uu____63698 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____63698  in
                        if uu____63696
                        then
                          let uu____63712 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____63712
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____63735 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____63735))
                        else
                          (let uu____63750 =
                             FStar_Syntax_Util.is_total_comp c1  in
                           if uu____63750
                           then
                             let close1 x reason c =
                               let x1 =
                                 let uu___1049_63792 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1049_63792.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1049_63792.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (FStar_Syntax_Util.comp_result c1)
                                 }  in
                               let uu____63793 =
                                 let uu____63799 =
                                   close_comp_if_refinement_t env
                                     x1.FStar_Syntax_Syntax.sort x1 c
                                    in
                                 (uu____63799, reason)  in
                               FStar_Util.Inl uu____63793  in
                             match (e1opt, b) with
                             | (FStar_Pervasives_Native.Some
                                e,FStar_Pervasives_Native.Some x) ->
                                 let uu____63835 =
                                   FStar_All.pipe_right c2
                                     (FStar_Syntax_Subst.subst_comp
                                        [FStar_Syntax_Syntax.NT (x, e)])
                                    in
                                 FStar_All.pipe_right uu____63835
                                   (close1 x "c1 Tot")
                             | (uu____63849,FStar_Pervasives_Native.Some x)
                                 ->
                                 FStar_All.pipe_right c2
                                   (close1 x "c1 Tot only close")
                             | (uu____63872,uu____63873) -> aux ()
                           else
                             (let uu____63888 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____63888
                              then
                                let uu____63901 =
                                  let uu____63907 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____63907, "both GTot")  in
                                FStar_Util.Inl uu____63901
                              else aux ()))
                         in
                      let uu____63918 = try_simplify ()  in
                      match uu____63918 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____63944  ->
                                let uu____63945 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____63945);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____63959  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____63981 = lift_and_destruct env c11 c21
                                 in
                              match uu____63981 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____64034 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____64034]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____64054 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____64054]
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
                                    let uu____64101 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____64110 =
                                      let uu____64121 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____64130 =
                                        let uu____64141 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____64150 =
                                          let uu____64161 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____64170 =
                                            let uu____64181 =
                                              let uu____64190 = mk_lam wp2
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____64190
                                               in
                                            [uu____64181]  in
                                          uu____64161 :: uu____64170  in
                                        uu____64141 :: uu____64150  in
                                      uu____64121 :: uu____64130  in
                                    uu____64101 :: uu____64110  in
                                  let wp =
                                    let uu____64242 =
                                      let uu____64247 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____64247 wp_args
                                       in
                                    uu____64242 FStar_Pervasives_Native.None
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
                              let uu____64270 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____64270 with
                              | (m,uu____64278,lift2) ->
                                  let c23 =
                                    let uu____64281 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____64281
                                     in
                                  let uu____64282 = destruct_comp c12  in
                                  (match uu____64282 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____64296 =
                                           let uu____64301 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____64302 =
                                             let uu____64303 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____64312 =
                                               let uu____64323 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____64323]  in
                                             uu____64303 :: uu____64312  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____64301 uu____64302
                                            in
                                         uu____64296
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
                            let uu____64361 = destruct_comp c1_typ  in
                            match uu____64361 with
                            | (u_res_t1,res_t1,uu____64370) ->
                                let uu____64371 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____64371
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____64376 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____64376
                                   then
                                     (debug1
                                        (fun uu____64386  ->
                                           let uu____64387 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____64389 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____64387 uu____64389);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____64397 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____64400 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____64400)
                                         in
                                      if uu____64397
                                      then
                                        let e1' =
                                          let uu____64421 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____64421
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____64433  ->
                                              let uu____64434 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____64436 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____64434 uu____64436);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____64451  ->
                                              let uu____64452 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____64454 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____64452 uu____64454);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____64461 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____64461
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
      | uu____64479 -> g2
  
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
            (let uu____64503 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____64503)
           in
        let flags =
          if should_return1
          then
            let uu____64511 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____64511
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____64527 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____64531 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____64531
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____64537 =
              let uu____64539 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____64539  in
            (if uu____64537
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___1168_64546 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___1168_64546.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___1168_64546.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___1168_64546.FStar_Syntax_Syntax.effect_args);
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
               let uu____64559 =
                 let uu____64560 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____64560
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                 uu____64559
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____64563 =
               let uu____64564 =
                 let uu____64565 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____64565
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____64564  in
             FStar_Syntax_Util.comp_set_flags uu____64563 flags)
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
            fun uu____64603  ->
              match uu____64603 with
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
                    let uu____64615 =
                      ((let uu____64619 = is_pure_or_ghost_effect env eff1
                           in
                        Prims.op_Negation uu____64619) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____64615
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____64637 =
        let uu____64638 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____64638  in
      FStar_Syntax_Syntax.fvar uu____64637 FStar_Syntax_Syntax.delta_constant
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
               fun uu____64708  ->
                 match uu____64708 with
                 | (uu____64722,eff_label,uu____64724,uu____64725) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____64738 =
          let uu____64746 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____64784  ->
                    match uu____64784 with
                    | (uu____64799,uu____64800,flags,uu____64802) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___590_64819  ->
                                match uu___590_64819 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____64822 -> false))))
             in
          if uu____64746
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____64738 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____64855 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____64857 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____64857
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____64898 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____64899 =
                     let uu____64904 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____64905 =
                       let uu____64906 = FStar_Syntax_Syntax.as_arg res_t1
                          in
                       let uu____64915 =
                         let uu____64926 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____64935 =
                           let uu____64946 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____64955 =
                             let uu____64966 =
                               FStar_Syntax_Syntax.as_arg wp_e  in
                             [uu____64966]  in
                           uu____64946 :: uu____64955  in
                         uu____64926 :: uu____64935  in
                       uu____64906 :: uu____64915  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____64904 uu____64905
                      in
                   uu____64899 FStar_Pervasives_Native.None uu____64898  in
                 let default_case =
                   let post_k =
                     let uu____65019 =
                       let uu____65028 =
                         FStar_Syntax_Syntax.null_binder res_t  in
                       [uu____65028]  in
                     let uu____65047 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____65019 uu____65047  in
                   let kwp =
                     let uu____65053 =
                       let uu____65062 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____65062]  in
                     let uu____65081 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____65053 uu____65081  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____65088 =
                       let uu____65089 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____65089]  in
                     let uu____65108 =
                       let uu____65111 =
                         let uu____65118 =
                           FStar_TypeChecker_Env.get_range env  in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____65118
                          in
                       let uu____65119 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____65111 uu____65119  in
                     FStar_Syntax_Util.abs uu____65088 uu____65108
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
                   let uu____65143 =
                     should_not_inline_whole_match ||
                       (let uu____65146 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____65146)
                      in
                   if uu____65143 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____65185  ->
                        fun celse  ->
                          match uu____65185 with
                          | (g,eff_label,uu____65202,cthen) ->
                              let uu____65216 =
                                let uu____65241 =
                                  let uu____65242 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____65242
                                   in
                                lift_and_destruct env uu____65241 celse  in
                              (match uu____65216 with
                               | ((md,uu____65244,uu____65245),(uu____65246,uu____65247,wp_then),
                                  (uu____65249,uu____65250,wp_else)) ->
                                   let uu____65270 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____65270 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____65285::[] -> comp
                 | uu____65328 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____65347 = destruct_comp comp1  in
                     (match uu____65347 with
                      | (uu____65354,uu____65355,wp) ->
                          let wp1 =
                            let uu____65360 =
                              let uu____65365 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____65366 =
                                let uu____65367 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____65376 =
                                  let uu____65387 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____65387]  in
                                uu____65367 :: uu____65376  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____65365
                                uu____65366
                               in
                            uu____65360 FStar_Pervasives_Native.None
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
          let uu____65453 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____65453 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____65469 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____65475 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____65469 uu____65475
              else
                (let uu____65484 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____65490 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____65484 uu____65490)
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
          let uu____65515 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____65515
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____65518 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____65518
        then u_res
        else
          (let is_total =
             let uu____65525 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____65525
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____65536 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____65536 with
              | FStar_Pervasives_Native.None  ->
                  let uu____65539 =
                    let uu____65545 =
                      let uu____65547 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____65547
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____65545)
                     in
                  FStar_Errors.raise_error uu____65539
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
               let uu____65592 =
                 let uu____65593 = FStar_Syntax_Subst.compress t2  in
                 uu____65593.FStar_Syntax_Syntax.n  in
               match uu____65592 with
               | FStar_Syntax_Syntax.Tm_type uu____65597 -> true
               | uu____65599 -> false  in
             let uu____65601 =
               let uu____65602 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____65602.FStar_Syntax_Syntax.n  in
             match uu____65601 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____65610 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____65620 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____65620
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____65623 =
                     let uu____65624 =
                       let uu____65625 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____65625
                        in
                     (FStar_Pervasives_Native.None, uu____65624)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____65623
                    in
                 let e1 =
                   let uu____65631 =
                     let uu____65636 =
                       let uu____65637 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____65637]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____65636  in
                   uu____65631 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____65662 -> (e, lc))
  
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
          (let uu____65697 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____65697
           then
             let uu____65700 = FStar_Syntax_Print.term_to_string e  in
             let uu____65702 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____65704 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____65700 uu____65702 uu____65704
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____65714 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____65714 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____65739 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____65765 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____65765, false)
             else
               (let uu____65775 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____65775, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____65788) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____65800 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____65800
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___1324_65816 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___1324_65816.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___1324_65816.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___1324_65816.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____65823 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____65823 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____65835 =
                      let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                      let res_t = FStar_Syntax_Util.comp_result c  in
                      let set_result_typ1 c1 =
                        FStar_Syntax_Util.set_result_typ c1 t  in
                      let uu____65846 =
                        let uu____65848 = FStar_Syntax_Util.eq_tm t res_t  in
                        uu____65848 = FStar_Syntax_Util.Equal  in
                      if uu____65846
                      then
                        ((let uu____65851 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____65851
                          then
                            let uu____65855 =
                              FStar_Syntax_Print.term_to_string res_t  in
                            let uu____65857 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print2
                              "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                              uu____65855 uu____65857
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
                           | FStar_Syntax_Syntax.Tm_refine uu____65868 ->
                               true
                           | uu____65876 -> false  in
                         if is_res_t_refinement
                         then
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (res_t.FStar_Syntax_Syntax.pos)) res_t
                              in
                           let cret =
                             let uu____65881 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             return_value env (comp_univ_opt c) res_t
                               uu____65881
                              in
                           let lc1 =
                             let uu____65883 =
                               FStar_Syntax_Util.lcomp_of_comp c  in
                             let uu____65884 =
                               let uu____65885 =
                                 FStar_Syntax_Util.lcomp_of_comp cret  in
                               ((FStar_Pervasives_Native.Some x),
                                 uu____65885)
                                in
                             bind e.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some e) uu____65883
                               uu____65884
                              in
                           ((let uu____65889 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____65889
                             then
                               let uu____65893 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____65895 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               let uu____65897 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____65899 =
                                 FStar_Syntax_Print.lcomp_to_string lc1  in
                               FStar_Util.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu____65893 uu____65895 uu____65897
                                 uu____65899
                             else ());
                            (let uu____65904 =
                               FStar_Syntax_Syntax.lcomp_comp lc1  in
                             set_result_typ1 uu____65904))
                         else
                           ((let uu____65908 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____65908
                             then
                               let uu____65912 =
                                 FStar_Syntax_Print.term_to_string res_t  in
                               let uu____65914 =
                                 FStar_Syntax_Print.comp_to_string c  in
                               FStar_Util.print2
                                 "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                 uu____65912 uu____65914
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
                      let uu___1356_65922 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1356_65922.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1356_65922.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1356_65922.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____65928 =
                      let uu____65929 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____65929
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____65935 =
                           let uu____65936 = FStar_Syntax_Subst.compress f1
                              in
                           uu____65936.FStar_Syntax_Syntax.n  in
                         match uu____65935 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____65939,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____65941;
                                            FStar_Syntax_Syntax.vars =
                                              uu____65942;_},uu____65943)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1372_65969 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___1372_65969.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___1372_65969.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___1372_65969.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____65970 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____65973 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____65973
                               then
                                 let uu____65977 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____65979 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____65981 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____65983 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____65977 uu____65979 uu____65981
                                   uu____65983
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
                                   let uu____65996 =
                                     let uu____66001 =
                                       let uu____66002 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____66002]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____66001
                                      in
                                   uu____65996 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____66029 =
                                 let uu____66034 =
                                   FStar_All.pipe_left
                                     (fun _66055  ->
                                        FStar_Pervasives_Native.Some _66055)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____66056 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____66057 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____66058 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____66034
                                   uu____66056 e uu____66057 uu____66058
                                  in
                               match uu____66029 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___1388_66062 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___1388_66062.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___1388_66062.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____66064 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____66064
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____66069 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____66069
                                     then
                                       let uu____66073 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____66073
                                     else ());
                                    c2))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___591_66086  ->
                              match uu___591_66086 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____66089 -> []))
                       in
                    let lc1 =
                      let uu____66091 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____66091 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1402_66093 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___1402_66093.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___1402_66093.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___1402_66093.FStar_TypeChecker_Env.implicits)
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
        let uu____66129 =
          let uu____66132 =
            let uu____66137 =
              let uu____66138 =
                let uu____66147 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____66147  in
              [uu____66138]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____66137  in
          uu____66132 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____66129  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____66170 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____66170
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____66189 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____66205 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____66222 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____66222
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____66238)::(ens,uu____66240)::uu____66241 ->
                    let uu____66284 =
                      let uu____66287 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____66287  in
                    let uu____66288 =
                      let uu____66289 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____66289  in
                    (uu____66284, uu____66288)
                | uu____66292 ->
                    let uu____66303 =
                      let uu____66309 =
                        let uu____66311 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____66311
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____66309)
                       in
                    FStar_Errors.raise_error uu____66303
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____66331)::uu____66332 ->
                    let uu____66359 =
                      let uu____66364 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____66364
                       in
                    (match uu____66359 with
                     | (us_r,uu____66396) ->
                         let uu____66397 =
                           let uu____66402 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____66402
                            in
                         (match uu____66397 with
                          | (us_e,uu____66434) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____66437 =
                                  let uu____66438 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____66438
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____66437
                                  us_r
                                 in
                              let as_ens =
                                let uu____66440 =
                                  let uu____66441 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____66441
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____66440
                                  us_e
                                 in
                              let req =
                                let uu____66445 =
                                  let uu____66450 =
                                    let uu____66451 =
                                      let uu____66462 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____66462]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____66451
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____66450
                                   in
                                uu____66445 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____66502 =
                                  let uu____66507 =
                                    let uu____66508 =
                                      let uu____66519 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____66519]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____66508
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____66507
                                   in
                                uu____66502 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____66556 =
                                let uu____66559 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____66559  in
                              let uu____66560 =
                                let uu____66561 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____66561  in
                              (uu____66556, uu____66560)))
                | uu____66564 -> failwith "Impossible"))
  
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
      (let uu____66598 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____66598
       then
         let uu____66603 = FStar_Syntax_Print.term_to_string tm  in
         let uu____66605 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____66603
           uu____66605
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
        (let uu____66659 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____66659
         then
           let uu____66664 = FStar_Syntax_Print.term_to_string tm  in
           let uu____66666 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____66664
             uu____66666
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____66677 =
      let uu____66679 =
        let uu____66680 = FStar_Syntax_Subst.compress t  in
        uu____66680.FStar_Syntax_Syntax.n  in
      match uu____66679 with
      | FStar_Syntax_Syntax.Tm_app uu____66684 -> false
      | uu____66702 -> true  in
    if uu____66677
    then t
    else
      (let uu____66707 = FStar_Syntax_Util.head_and_args t  in
       match uu____66707 with
       | (head1,args) ->
           let uu____66750 =
             let uu____66752 =
               let uu____66753 = FStar_Syntax_Subst.compress head1  in
               uu____66753.FStar_Syntax_Syntax.n  in
             match uu____66752 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____66758 -> false  in
           if uu____66750
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____66790 ->
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
          ((let uu____66837 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____66837
            then
              let uu____66840 = FStar_Syntax_Print.term_to_string e  in
              let uu____66842 = FStar_Syntax_Print.term_to_string t  in
              let uu____66844 =
                let uu____66846 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____66846
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____66840 uu____66842 uu____66844
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____66859 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____66859 with
              | (formals,uu____66875) ->
                  let n_implicits =
                    let uu____66897 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____66975  ->
                              match uu____66975 with
                              | (uu____66983,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____66990 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____66990 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____66897 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____67115 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____67115 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____67129 =
                      let uu____67135 =
                        let uu____67137 = FStar_Util.string_of_int n_expected
                           in
                        let uu____67139 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____67141 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____67137 uu____67139 uu____67141
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____67135)
                       in
                    let uu____67145 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____67129 uu____67145
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___592_67163 =
              match uu___592_67163 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____67206 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____67206 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _67337,uu____67324)
                           when _67337 = (Prims.parse_int "0") ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____67370,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____67372))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____67406 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____67406 with
                            | (v1,uu____67447,g) ->
                                ((let uu____67462 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____67462
                                  then
                                    let uu____67465 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____67465
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____67475 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____67475 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____67568 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____67568))))
                       | (uu____67595,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____67632 =
                             let uu____67645 =
                               let uu____67652 =
                                 let uu____67657 = FStar_Dyn.mkdyn env  in
                                 (uu____67657, tau)  in
                               FStar_Pervasives_Native.Some uu____67652  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____67645
                              in
                           (match uu____67632 with
                            | (v1,uu____67690,g) ->
                                ((let uu____67705 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____67705
                                  then
                                    let uu____67708 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____67708
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____67718 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____67718 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____67811 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____67811))))
                       | (uu____67838,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____67886 =
                       let uu____67913 = inst_n_binders t1  in
                       aux [] uu____67913 bs1  in
                     (match uu____67886 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____67985) -> (e, torig, guard)
                           | (uu____68016,[]) when
                               let uu____68047 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____68047 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____68049 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____68077 ->
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
            | uu____68090 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____68102 =
      let uu____68106 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____68106
        (FStar_List.map
           (fun u  ->
              let uu____68118 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____68118 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____68102 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____68146 = FStar_Util.set_is_empty x  in
      if uu____68146
      then []
      else
        (let s =
           let uu____68164 =
             let uu____68167 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____68167  in
           FStar_All.pipe_right uu____68164 FStar_Util.set_elements  in
         (let uu____68183 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____68183
          then
            let uu____68188 =
              let uu____68190 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____68190  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____68188
          else ());
         (let r =
            let uu____68199 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____68199  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____68238 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____68238
                     then
                       let uu____68243 =
                         let uu____68245 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____68245
                          in
                       let uu____68249 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____68251 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____68243 uu____68249 uu____68251
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
        let uu____68281 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____68281 FStar_Util.set_elements  in
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
        | ([],uu____68320) -> generalized_univ_names
        | (uu____68327,[]) -> explicit_univ_names
        | uu____68334 ->
            let uu____68343 =
              let uu____68349 =
                let uu____68351 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____68351
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____68349)
               in
            FStar_Errors.raise_error uu____68343 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____68373 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____68373
       then
         let uu____68378 = FStar_Syntax_Print.term_to_string t  in
         let uu____68380 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____68378 uu____68380
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____68389 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____68389
        then
          let uu____68394 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____68394
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____68403 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____68403
         then
           let uu____68408 = FStar_Syntax_Print.term_to_string t  in
           let uu____68410 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____68408 uu____68410
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
        let uu____68494 =
          let uu____68496 =
            FStar_Util.for_all
              (fun uu____68510  ->
                 match uu____68510 with
                 | (uu____68520,uu____68521,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____68496  in
        if uu____68494
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____68573 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____68573
              then
                let uu____68576 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____68576
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____68583 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____68583
               then
                 let uu____68586 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____68586
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____68604 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____68604 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____68638 =
             match uu____68638 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____68675 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____68675
                   then
                     let uu____68680 =
                       let uu____68682 =
                         let uu____68686 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____68686
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____68682
                         (FStar_String.concat ", ")
                        in
                     let uu____68734 =
                       let uu____68736 =
                         let uu____68740 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____68740
                           (FStar_List.map
                              (fun u  ->
                                 let uu____68753 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____68755 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____68753
                                   uu____68755))
                          in
                       FStar_All.pipe_right uu____68736
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____68680
                       uu____68734
                   else ());
                  (let univs2 =
                     let uu____68769 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____68781 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____68781) univs1
                       uu____68769
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____68788 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____68788
                    then
                      let uu____68793 =
                        let uu____68795 =
                          let uu____68799 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____68799
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____68795
                          (FStar_String.concat ", ")
                         in
                      let uu____68847 =
                        let uu____68849 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____68863 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____68865 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____68863
                                    uu____68865))
                           in
                        FStar_All.pipe_right uu____68849
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____68793 uu____68847
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____68886 =
             let uu____68903 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____68903  in
           match uu____68886 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____68993 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____68993
                 then ()
                 else
                   (let uu____68998 = lec_hd  in
                    match uu____68998 with
                    | (lb1,uu____69006,uu____69007) ->
                        let uu____69008 = lec2  in
                        (match uu____69008 with
                         | (lb2,uu____69016,uu____69017) ->
                             let msg =
                               let uu____69020 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____69022 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____69020 uu____69022
                                in
                             let uu____69025 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____69025))
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
                 let uu____69093 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____69093
                 then ()
                 else
                   (let uu____69098 = lec_hd  in
                    match uu____69098 with
                    | (lb1,uu____69106,uu____69107) ->
                        let uu____69108 = lec2  in
                        (match uu____69108 with
                         | (lb2,uu____69116,uu____69117) ->
                             let msg =
                               let uu____69120 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____69122 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____69120 uu____69122
                                in
                             let uu____69125 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____69125))
                  in
               let lecs1 =
                 let uu____69136 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____69189 = univs_and_uvars_of_lec this_lec  in
                        match uu____69189 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____69136 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____69294 = lec_hd  in
                   match uu____69294 with
                   | (lbname,e,c) ->
                       let uu____69304 =
                         let uu____69310 =
                           let uu____69312 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____69314 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____69316 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____69312 uu____69314 uu____69316
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____69310)
                          in
                       let uu____69320 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____69304 uu____69320
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____69339 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____69339 with
                         | FStar_Pervasives_Native.Some uu____69348 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____69356 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____69360 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____69360 with
                              | (bs,kres) ->
                                  ((let uu____69404 =
                                      let uu____69405 =
                                        let uu____69408 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____69408
                                         in
                                      uu____69405.FStar_Syntax_Syntax.n  in
                                    match uu____69404 with
                                    | FStar_Syntax_Syntax.Tm_type uu____69409
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____69413 =
                                          let uu____69415 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____69415  in
                                        if uu____69413
                                        then fail1 kres
                                        else ()
                                    | uu____69420 -> fail1 kres);
                                   (let a =
                                      let uu____69422 =
                                        let uu____69425 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _69428  ->
                                             FStar_Pervasives_Native.Some
                                               _69428) uu____69425
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____69422
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____69436 ->
                                          let uu____69445 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____69445
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
                      (fun uu____69548  ->
                         match uu____69548 with
                         | (lbname,e,c) ->
                             let uu____69594 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____69655 ->
                                   let uu____69668 = (e, c)  in
                                   (match uu____69668 with
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
                                                (fun uu____69708  ->
                                                   match uu____69708 with
                                                   | (x,uu____69714) ->
                                                       let uu____69715 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____69715)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____69733 =
                                                let uu____69735 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____69735
                                                 in
                                              if uu____69733
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
                                          let uu____69744 =
                                            let uu____69745 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____69745.FStar_Syntax_Syntax.n
                                             in
                                          match uu____69744 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____69770 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____69770 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____69781 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____69785 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____69785, gen_tvars))
                                in
                             (match uu____69594 with
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
        (let uu____69932 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____69932
         then
           let uu____69935 =
             let uu____69937 =
               FStar_List.map
                 (fun uu____69952  ->
                    match uu____69952 with
                    | (lb,uu____69961,uu____69962) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____69937 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____69935
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____69988  ->
                match uu____69988 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____70017 = gen env is_rec lecs  in
           match uu____70017 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____70116  ->
                       match uu____70116 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____70178 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____70178
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____70226  ->
                           match uu____70226 with
                           | (l,us,e,c,gvs) ->
                               let uu____70260 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____70262 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____70264 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____70266 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____70268 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____70260 uu____70262 uu____70264
                                 uu____70266 uu____70268))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____70313  ->
                match uu____70313 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____70357 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____70357, t, c, gvs)) univnames_lecs
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
              (let uu____70418 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____70418 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____70424 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _70427  -> FStar_Pervasives_Native.Some _70427)
                     uu____70424)
             in
          let is_var e1 =
            let uu____70435 =
              let uu____70436 = FStar_Syntax_Subst.compress e1  in
              uu____70436.FStar_Syntax_Syntax.n  in
            match uu____70435 with
            | FStar_Syntax_Syntax.Tm_name uu____70440 -> true
            | uu____70442 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1858_70463 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1858_70463.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1858_70463.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____70464 -> e2  in
          let env2 =
            let uu___1861_70466 = env1  in
            let uu____70467 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1861_70466.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1861_70466.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1861_70466.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1861_70466.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1861_70466.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1861_70466.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1861_70466.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1861_70466.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1861_70466.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1861_70466.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___1861_70466.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1861_70466.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1861_70466.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1861_70466.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1861_70466.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1861_70466.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1861_70466.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____70467;
              FStar_TypeChecker_Env.is_iface =
                (uu___1861_70466.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1861_70466.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1861_70466.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1861_70466.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1861_70466.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1861_70466.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1861_70466.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1861_70466.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1861_70466.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1861_70466.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1861_70466.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1861_70466.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1861_70466.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1861_70466.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1861_70466.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1861_70466.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1861_70466.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1861_70466.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1861_70466.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___1861_70466.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1861_70466.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1861_70466.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1861_70466.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1861_70466.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1861_70466.FStar_TypeChecker_Env.nbe)
            }  in
          let uu____70469 = check1 env2 t1 t2  in
          match uu____70469 with
          | FStar_Pervasives_Native.None  ->
              let uu____70476 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____70482 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____70476 uu____70482
          | FStar_Pervasives_Native.Some g ->
              ((let uu____70489 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____70489
                then
                  let uu____70494 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____70494
                else ());
               (let uu____70500 = decorate e t2  in (uu____70500, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____70528 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____70528
         then
           let uu____70531 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____70531
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____70545 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____70545
         then
           let uu____70553 = discharge g1  in
           let uu____70555 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____70553, uu____70555)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.NoFullNorm;
              FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____70564 =
                let uu____70565 =
                  let uu____70566 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____70566
                    FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____70565
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____70564
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____70568 = destruct_comp c1  in
            match uu____70568 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____70586 = FStar_TypeChecker_Env.get_range env  in
                  let uu____70587 =
                    let uu____70592 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____70593 =
                      let uu____70594 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____70603 =
                        let uu____70614 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____70614]  in
                      uu____70594 :: uu____70603  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____70592 uu____70593  in
                  uu____70587 FStar_Pervasives_Native.None uu____70586  in
                ((let uu____70648 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____70648
                  then
                    let uu____70653 = FStar_Syntax_Print.term_to_string vc
                       in
                    FStar_Util.print1 "top-level VC: %s\n" uu____70653
                  else ());
                 (let g2 =
                    let uu____70659 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____70659  in
                  let uu____70660 = discharge g2  in
                  let uu____70662 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____70660, uu____70662)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___593_70696 =
        match uu___593_70696 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____70706)::[] -> f fst1
        | uu____70731 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____70743 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____70743
          (fun _70744  -> FStar_TypeChecker_Common.NonTrivial _70744)
         in
      let op_or_e e =
        let uu____70755 =
          let uu____70756 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____70756  in
        FStar_All.pipe_right uu____70755
          (fun _70759  -> FStar_TypeChecker_Common.NonTrivial _70759)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _70766  -> FStar_TypeChecker_Common.NonTrivial _70766)
         in
      let op_or_t t =
        let uu____70777 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____70777
          (fun _70780  -> FStar_TypeChecker_Common.NonTrivial _70780)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _70787  -> FStar_TypeChecker_Common.NonTrivial _70787)
         in
      let short_op_ite uu___594_70793 =
        match uu___594_70793 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____70803)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____70830)::[] ->
            let uu____70871 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____70871
              (fun _70872  -> FStar_TypeChecker_Common.NonTrivial _70872)
        | uu____70873 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____70885 =
          let uu____70893 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____70893)  in
        let uu____70901 =
          let uu____70911 =
            let uu____70919 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____70919)  in
          let uu____70927 =
            let uu____70937 =
              let uu____70945 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____70945)  in
            let uu____70953 =
              let uu____70963 =
                let uu____70971 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____70971)  in
              let uu____70979 =
                let uu____70989 =
                  let uu____70997 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____70997)  in
                [uu____70989; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____70963 :: uu____70979  in
            uu____70937 :: uu____70953  in
          uu____70911 :: uu____70927  in
        uu____70885 :: uu____70901  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____71059 =
            FStar_Util.find_map table
              (fun uu____71074  ->
                 match uu____71074 with
                 | (x,mk1) ->
                     let uu____71091 = FStar_Ident.lid_equals x lid  in
                     if uu____71091
                     then
                       let uu____71096 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____71096
                     else FStar_Pervasives_Native.None)
             in
          (match uu____71059 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____71100 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____71108 =
      let uu____71109 = FStar_Syntax_Util.un_uinst l  in
      uu____71109.FStar_Syntax_Syntax.n  in
    match uu____71108 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____71114 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____71150)::uu____71151 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____71170 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____71179,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____71180))::uu____71181 -> bs
      | uu____71199 ->
          let uu____71200 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____71200 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____71204 =
                 let uu____71205 = FStar_Syntax_Subst.compress t  in
                 uu____71205.FStar_Syntax_Syntax.n  in
               (match uu____71204 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____71209) ->
                    let uu____71230 =
                      FStar_Util.prefix_until
                        (fun uu___595_71270  ->
                           match uu___595_71270 with
                           | (uu____71278,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____71279)) ->
                               false
                           | uu____71284 -> true) bs'
                       in
                    (match uu____71230 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____71320,uu____71321) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____71393,uu____71394) ->
                         let uu____71467 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____71487  ->
                                   match uu____71487 with
                                   | (x,uu____71496) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____71467
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____71545  ->
                                     match uu____71545 with
                                     | (x,i) ->
                                         let uu____71564 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____71564, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____71575 -> bs))
  
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
            let uu____71604 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____71604
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
          let uu____71635 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____71635
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
        (let uu____71678 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____71678
         then
           ((let uu____71683 = FStar_Ident.text_of_lid lident  in
             d uu____71683);
            (let uu____71685 = FStar_Ident.text_of_lid lident  in
             let uu____71687 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____71685 uu____71687))
         else ());
        (let fv =
           let uu____71693 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____71693
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
         let uu____71705 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2019_71707 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2019_71707.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2019_71707.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2019_71707.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2019_71707.FStar_Syntax_Syntax.sigattrs)
           }), uu____71705))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___596_71725 =
        match uu___596_71725 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____71728 -> false  in
      let reducibility uu___597_71736 =
        match uu___597_71736 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____71743 -> false  in
      let assumption uu___598_71751 =
        match uu___598_71751 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____71755 -> false  in
      let reification uu___599_71763 =
        match uu___599_71763 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____71766 -> true
        | uu____71768 -> false  in
      let inferred uu___600_71776 =
        match uu___600_71776 with
        | FStar_Syntax_Syntax.Discriminator uu____71778 -> true
        | FStar_Syntax_Syntax.Projector uu____71780 -> true
        | FStar_Syntax_Syntax.RecordType uu____71786 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____71796 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____71809 -> false  in
      let has_eq uu___601_71817 =
        match uu___601_71817 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____71821 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____71900 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____71907 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____71918 =
        let uu____71920 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___602_71926  ->
                  match uu___602_71926 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____71929 -> false))
           in
        FStar_All.pipe_right uu____71920 Prims.op_Negation  in
      if uu____71918
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____71950 =
            let uu____71956 =
              let uu____71958 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____71958 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____71956)  in
          FStar_Errors.raise_error uu____71950 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____71976 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____71984 =
            let uu____71986 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____71986  in
          if uu____71984 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____71996),uu____71997) ->
              ((let uu____72009 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____72009
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____72018 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____72018
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____72029 ->
              let uu____72038 =
                let uu____72040 =
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
                Prims.op_Negation uu____72040  in
              if uu____72038 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____72050 ->
              let uu____72057 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____72057 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____72065 ->
              let uu____72072 =
                let uu____72074 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____72074  in
              if uu____72072 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____72084 ->
              let uu____72085 =
                let uu____72087 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____72087  in
              if uu____72085 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____72097 ->
              let uu____72098 =
                let uu____72100 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____72100  in
              if uu____72098 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____72110 ->
              let uu____72123 =
                let uu____72125 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____72125  in
              if uu____72123 then err'1 () else ()
          | uu____72135 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let has_erased_for_extraction_attr fv =
        let uu____72158 =
          let uu____72163 =
            FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
          FStar_All.pipe_right uu____72163
            (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
           in
        FStar_All.pipe_right uu____72158
          (fun l_opt  ->
             (FStar_Util.is_some l_opt) &&
               (let uu____72182 = FStar_All.pipe_right l_opt FStar_Util.must
                   in
                FStar_All.pipe_right uu____72182
                  (FStar_List.existsb
                     (fun t1  ->
                        let uu____72200 =
                          let uu____72201 = FStar_Syntax_Subst.compress t1
                             in
                          uu____72201.FStar_Syntax_Syntax.n  in
                        match uu____72200 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            FStar_Ident.lid_equals
                              (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              FStar_Parser_Const.must_erase_for_extraction_attr
                            -> true
                        | uu____72207 -> false))))
         in
      let rec aux_whnf env t1 =
        let uu____72233 =
          let uu____72234 = FStar_Syntax_Subst.compress t1  in
          uu____72234.FStar_Syntax_Syntax.n  in
        match uu____72233 with
        | FStar_Syntax_Syntax.Tm_type uu____72238 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (has_erased_for_extraction_attr fv)
        | FStar_Syntax_Syntax.Tm_arrow uu____72241 ->
            let uu____72256 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____72256 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____72289 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____72289
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____72295;
               FStar_Syntax_Syntax.index = uu____72296;
               FStar_Syntax_Syntax.sort = t2;_},uu____72298)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____72307,uu____72308) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____72350::[]) ->
            let uu____72389 =
              let uu____72390 = FStar_Syntax_Util.un_uinst head1  in
              uu____72390.FStar_Syntax_Syntax.n  in
            (match uu____72389 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.erased_lid)
                   || (has_erased_for_extraction_attr fv)
             | uu____72395 -> false)
        | uu____72397 -> false
      
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
        (let uu____72407 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____72407
         then
           let uu____72412 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____72412
         else ());
        res
       in aux g t
  