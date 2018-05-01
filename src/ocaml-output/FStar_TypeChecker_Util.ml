open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____21 = FStar_TypeChecker_Env.get_range env  in
      let uu____22 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____21 uu____22
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.binding Prims.list ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term'
                                            FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2)
  =
  fun reason  ->
    fun r  ->
      fun gamma  ->
        fun binders  ->
          fun k  ->
            let ctx_uvar =
              let uu____79 = FStar_Syntax_Unionfind.fresh ()  in
              {
                FStar_Syntax_Syntax.ctx_uvar_head = uu____79;
                FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                FStar_Syntax_Syntax.ctx_uvar_typ = k;
                FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                FStar_Syntax_Syntax.ctx_uvar_should_check = true;
                FStar_Syntax_Syntax.ctx_uvar_range = r
              }  in
            FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true
              gamma binders;
            (let uu____91 =
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_uvar)
                 FStar_Pervasives_Native.None r
                in
             (ctx_uvar, uu____91))
  
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
          let uu____128 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid  in
          match uu____128 with
          | FStar_Pervasives_Native.Some (uu____151::(tm,uu____153)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____203 ->
              let binders = FStar_TypeChecker_Env.all_binders env  in
              let uu____215 =
                new_implicit_var_aux reason r env.FStar_TypeChecker_Env.gamma
                  binders k
                 in
              (match uu____215 with
               | (ctx_uvar,t) ->
                   let g =
                     let uu___124_241 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___124_241.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___124_241.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___124_241.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         [(reason, t, ctx_uvar, r, true)]
                     }  in
                   (t, [(ctx_uvar, r)], g))
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun xs  ->
      fun g  ->
        let rec aux x i =
          let uu____338 = i  in
          match uu____338 with
          | (reason,term,ctx_u,range,should_check) ->
              if Prims.op_Negation should_check
              then i
              else
                (let uu____385 =
                   FStar_Syntax_Unionfind.find
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 match uu____385 with
                 | FStar_Pervasives_Native.Some uu____400 ->
                     ((let uu____402 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____402
                       then
                         let uu____403 =
                           FStar_Syntax_Print.ctx_uvar_to_string ctx_u  in
                         FStar_Util.print1
                           "%s already solved; nothing to do\n" uu____403
                       else ());
                      i)
                 | FStar_Pervasives_Native.None  ->
                     let uu____405 =
                       FStar_Util.prefix_until
                         (fun uu___105_420  ->
                            match uu___105_420 with
                            | FStar_Syntax_Syntax.Binding_var uu____421 ->
                                true
                            | uu____422 -> false)
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma
                        in
                     (match uu____405 with
                      | FStar_Pervasives_Native.None  -> i
                      | FStar_Pervasives_Native.Some
                          (uu____445,hd1,gamma_tail) ->
                          (FStar_TypeChecker_Common.check_uvar_ctx_invariant
                             reason range should_check
                             ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma
                             ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders;
                           (match hd1 with
                            | FStar_Syntax_Syntax.Binding_var x' when
                                FStar_Syntax_Syntax.bv_eq x x' ->
                                let uu____480 =
                                  FStar_Util.prefix
                                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                   in
                                (match uu____480 with
                                 | (binders_pfx,uu____512) ->
                                     let typ =
                                       let uu____536 =
                                         let uu____543 =
                                           FStar_Syntax_Syntax.mk_binder x
                                            in
                                         [uu____543]  in
                                       let uu____556 =
                                         FStar_Syntax_Syntax.mk_Total
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                          in
                                       FStar_Syntax_Util.arrow uu____536
                                         uu____556
                                        in
                                     let uu____559 =
                                       new_implicit_var_aux reason range
                                         gamma_tail binders_pfx typ
                                        in
                                     (match uu____559 with
                                      | (ctx_v,t_v) ->
                                          let sol =
                                            let uu____587 =
                                              let uu____592 =
                                                let uu____593 =
                                                  let uu____600 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      x
                                                     in
                                                  FStar_Syntax_Syntax.as_arg
                                                    uu____600
                                                   in
                                                [uu____593]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                t_v uu____592
                                               in
                                            uu____587
                                              FStar_Pervasives_Native.None
                                              range
                                             in
                                          ((let uu____616 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other "Rel")
                                               in
                                            if uu____616
                                            then
                                              let uu____617 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              let uu____618 =
                                                FStar_Syntax_Print.ctx_uvar_to_string
                                                  ctx_u
                                                 in
                                              let uu____619 =
                                                FStar_Syntax_Print.term_to_string
                                                  sol
                                                 in
                                              FStar_Util.print3
                                                "Closing implicit %s with binder %s to %s\n"
                                                uu____617 uu____618 uu____619
                                            else ());
                                           FStar_Syntax_Unionfind.change
                                             ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                             sol;
                                           (reason, t_v, ctx_v, range,
                                             should_check))))
                            | uu____624 -> i))))
           in
        let uu____625 =
          FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
            (FStar_List.partition
               (fun uu____671  ->
                  match uu____671 with
                  | (uu____676,p) ->
                      FStar_TypeChecker_Rel.flex_prob_closing env xs p))
           in
        match uu____625 with
        | (solve_now,defer) ->
            ((let uu____705 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____705
              then
                (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                 FStar_List.iter
                   (fun uu____716  ->
                      match uu____716 with
                      | (s,p) ->
                          let uu____723 =
                            FStar_TypeChecker_Rel.prob_to_string env p  in
                          FStar_Util.print2 "%s: %s\n" s uu____723) solve_now;
                 FStar_Util.print_string " ...DEFERRED THE REST:\n";
                 FStar_List.iter
                   (fun uu____734  ->
                      match uu____734 with
                      | (s,p) ->
                          let uu____741 =
                            FStar_TypeChecker_Rel.prob_to_string env p  in
                          FStar_Util.print2 "%s: %s\n" s uu____741) defer;
                 FStar_Util.print_string "END\n")
              else ());
             (let g1 =
                FStar_TypeChecker_Rel.solve_deferred_constraints env
                  (let uu___125_745 = g  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___125_745.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = solve_now;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___125_745.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___125_745.FStar_TypeChecker_Env.implicits)
                   })
                 in
              let g2 =
                let uu___126_747 = g1  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___126_747.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred = defer;
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___126_747.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits =
                    (uu___126_747.FStar_TypeChecker_Env.implicits)
                }  in
              (let uu____749 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____749
               then
                 let uu____750 = FStar_Syntax_Print.binders_to_string ", " xs
                    in
                 FStar_Util.print1
                   "Starting to close implicits with binders {%s}\n"
                   uu____750
               else ());
              (let is =
                 FStar_List.fold_right
                   (fun uu____790  ->
                      fun is  ->
                        match uu____790 with
                        | (x,uu____825) ->
                            ((let uu____827 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____827
                              then
                                let uu____828 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.print1 "Considering closing %s\n"
                                  uu____828
                              else ());
                             FStar_List.map (aux x) is)) xs
                   g2.FStar_TypeChecker_Env.implicits
                  in
               let g3 =
                 let uu___127_855 = g2  in
                 {
                   FStar_TypeChecker_Env.guard_f =
                     (uu___127_855.FStar_TypeChecker_Env.guard_f);
                   FStar_TypeChecker_Env.deferred =
                     (uu___127_855.FStar_TypeChecker_Env.deferred);
                   FStar_TypeChecker_Env.univ_ineqs =
                     (uu___127_855.FStar_TypeChecker_Env.univ_ineqs);
                   FStar_TypeChecker_Env.implicits = is
                 }  in
               (let uu____857 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____857
                then
                  let uu____858 =
                    FStar_Syntax_Print.binders_to_string ", " xs  in
                  let uu____859 =
                    FStar_TypeChecker_Rel.guard_to_string env g3  in
                  FStar_Util.print2
                    "Closed implicits with binders {%s}; guard is\n\t%s\n"
                    uu____858 uu____859
                else ());
               g3)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____874 =
        let uu____875 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____875  in
      if uu____874
      then
        let us =
          let uu____877 =
            let uu____880 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____880
             in
          FStar_All.pipe_right uu____877 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____891 =
            let uu____896 =
              let uu____897 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____897
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____896)  in
          FStar_Errors.log_issue r uu____891);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____914  ->
      match uu____914 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____924;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____926;
          FStar_Syntax_Syntax.lbpos = uu____927;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____960 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____960 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____997) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____1004) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1059) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____1091 = FStar_Options.ml_ish ()  in
                                if uu____1091
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____1108 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____1108
                            then
                              let uu____1109 = FStar_Range.string_of_range r
                                 in
                              let uu____1110 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____1109 uu____1110
                            else ());
                           FStar_Util.Inl t2)
                      | uu____1112 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____1114 = aux e1  in
                      match uu____1114 with
                      | FStar_Util.Inr c ->
                          let uu____1120 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____1120
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____1122 =
                               let uu____1127 =
                                 let uu____1128 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____1128
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____1127)
                                in
                             FStar_Errors.raise_error uu____1122 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____1132 ->
               let uu____1133 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1133 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_TypeChecker_Env.env ->
           FStar_Syntax_Syntax.term ->
             (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
               FStar_Pervasives_Native.tuple2)
          ->
          (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,
            FStar_TypeChecker_Env.guard_t,FStar_Syntax_Syntax.pat)
            FStar_Pervasives_Native.tuple4)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        fun tc_annot  ->
          let check_bv env1 x =
            let uu____1227 =
              let uu____1232 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1232 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1237;
                  FStar_Syntax_Syntax.vars = uu____1238;_} ->
                  let uu____1241 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1241 with
                   | (t,uu____1251) ->
                       let uu____1252 =
                         let uu____1265 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         new_implicit_var "" uu____1265 env1 t  in
                       (match uu____1252 with | (t1,uu____1271,g) -> (t1, g)))
              | t -> tc_annot env1 t  in
            match uu____1227 with
            | (t_x,guard) ->
                ((let uu___128_1293 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___128_1293.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___128_1293.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = t_x
                  }), guard)
             in
          let rec pat_as_arg_with_env allow_wc_dependence env1 p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let e =
                  match c with
                  | FStar_Const.Const_int
                      (repr,FStar_Pervasives_Native.Some sw) ->
                      FStar_ToSyntax_ToSyntax.desugar_machine_integer
                        env1.FStar_TypeChecker_Env.dsenv repr sw
                        p1.FStar_Syntax_Syntax.p
                  | uu____1368 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1376) ->
                let uu____1381 = FStar_Syntax_Util.type_u ()  in
                (match uu____1381 with
                 | (k,uu____1407) ->
                     let uu____1408 =
                       let uu____1421 = FStar_Syntax_Syntax.range_of_bv x  in
                       new_implicit_var "" uu____1421 env1 k  in
                     (match uu____1408 with
                      | (t,uu____1443,g) ->
                          let x1 =
                            let uu___129_1458 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___129_1458.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___129_1458.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____1459 =
                            let uu____1472 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            new_implicit_var "" uu____1472 env1 t  in
                          (match uu____1459 with
                           | (e,uu____1494,g') ->
                               let p2 =
                                 let uu___130_1511 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___130_1511.FStar_Syntax_Syntax.p)
                                 }  in
                               let uu____1514 =
                                 FStar_TypeChecker_Rel.conj_guard g g'  in
                               ([], [], [], env1, e, uu____1514, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1522 = check_bv env1 x  in
                (match uu____1522 with
                 | (x1,g) ->
                     let env2 =
                       if allow_wc_dependence
                       then FStar_TypeChecker_Env.push_bv env1 x1
                       else env1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [], [x1], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_var x ->
                let uu____1561 = check_bv env1 x  in
                (match uu____1561 with
                 | (x1,g) ->
                     let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [x1], [], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let uu____1616 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1750  ->
                          fun uu____1751  ->
                            match (uu____1750, uu____1751) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1949 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1949 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____2025 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____2025, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1616 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____2156 =
                         let uu____2161 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____2162 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2161 uu____2162
                          in
                       uu____2156 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____2179 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____2190 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____2201 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____2179, uu____2190, uu____2201, env2, e, guard,
                       (let uu___131_2219 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___131_2219.FStar_Syntax_Syntax.p)
                        })))
             in
          let rec elaborate_pat env1 p1 =
            let maybe_dot inaccessible a r =
              if allow_implicits && inaccessible
              then
                FStar_Syntax_Syntax.withinfo
                  (FStar_Syntax_Syntax.Pat_dot_term
                     (a, FStar_Syntax_Syntax.tun)) r
              else
                FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                  r
               in
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let pats1 =
                  FStar_List.map
                    (fun uu____2319  ->
                       match uu____2319 with
                       | (p2,imp) ->
                           let uu____2338 = elaborate_pat env1 p2  in
                           (uu____2338, imp)) pats
                   in
                let uu____2343 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2343 with
                 | (uu____2350,t) ->
                     let uu____2352 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2352 with
                      | (f,uu____2368) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2494::uu____2495) ->
                                let uu____2538 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2538
                            | (uu____2547::uu____2548,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2626  ->
                                        match uu____2626 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2653 =
                                                     let uu____2656 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2656
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2653
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2658 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2658, true)
                                             | uu____2663 ->
                                                 let uu____2666 =
                                                   let uu____2671 =
                                                     let uu____2672 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2672
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2671)
                                                    in
                                                 let uu____2673 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2666 uu____2673)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2747,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2748)) when p_imp ->
                                     let uu____2751 = aux formals' pats'  in
                                     (p2, true) :: uu____2751
                                 | (uu____2768,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2776 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2776
                                        in
                                     let uu____2777 = aux formals' pats2  in
                                     (p3, true) :: uu____2777
                                 | (uu____2794,imp) ->
                                     let uu____2800 =
                                       let uu____2807 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2807)  in
                                     let uu____2810 = aux formals' pats'  in
                                     uu____2800 :: uu____2810)
                             in
                          let uu___132_2825 = p1  in
                          let uu____2828 =
                            let uu____2829 =
                              let uu____2842 = aux f pats1  in
                              (fv, uu____2842)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2829  in
                          {
                            FStar_Syntax_Syntax.v = uu____2828;
                            FStar_Syntax_Syntax.p =
                              (uu___132_2825.FStar_Syntax_Syntax.p)
                          }))
            | uu____2859 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2901 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2901 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2959 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2959 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2985 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2985
                       p3.FStar_Syntax_Syntax.p
                 | uu____3008 -> (b, a, w, arg, guard, p3))
             in
          let uu____3017 = one_pat true env p  in
          match uu____3017 with
          | (b,uu____3047,uu____3048,tm,guard,p1) -> (b, tm, guard, p1)
  
let (decorate_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      fun exp  ->
        let qq = p  in
        let rec aux p1 e =
          let pkg q = FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p
             in
          let e1 = FStar_Syntax_Util.unmeta e  in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____3110,FStar_Syntax_Syntax.Tm_uinst (e2,uu____3112)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____3117,uu____3118) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____3122 =
                    let uu____3123 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3124 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3123 uu____3124
                     in
                  failwith uu____3122)
               else ();
               (let uu____3127 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____3127
                then
                  let uu____3128 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____3129 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____3128
                    uu____3129
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___133_3133 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___133_3133.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___133_3133.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____3137 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____3137
                then
                  let uu____3138 =
                    let uu____3139 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3140 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3139 uu____3140
                     in
                  failwith uu____3138
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___134_3144 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___134_3144.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___134_3144.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____3146),uu____3147) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____3171 =
                  let uu____3172 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____3172  in
                if uu____3171
                then
                  let uu____3173 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3173
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____3192;
                FStar_Syntax_Syntax.vars = uu____3193;_},args))
              ->
              ((let uu____3232 =
                  let uu____3233 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3233 Prims.op_Negation  in
                if uu____3232
                then
                  let uu____3234 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3234
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3372)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3447) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3484) ->
                           let pat =
                             let uu____3506 = aux argpat e2  in
                             let uu____3507 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3506, uu____3507)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3512 ->
                      let uu____3535 =
                        let uu____3536 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3537 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3536 uu____3537
                         in
                      failwith uu____3535
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3547;
                     FStar_Syntax_Syntax.vars = uu____3548;_},uu____3549);
                FStar_Syntax_Syntax.pos = uu____3550;
                FStar_Syntax_Syntax.vars = uu____3551;_},args))
              ->
              ((let uu____3594 =
                  let uu____3595 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3595 Prims.op_Negation  in
                if uu____3594
                then
                  let uu____3596 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3596
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3734)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3809) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3846) ->
                           let pat =
                             let uu____3868 = aux argpat e2  in
                             let uu____3869 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3868, uu____3869)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3874 ->
                      let uu____3897 =
                        let uu____3898 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3899 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3898 uu____3899
                         in
                      failwith uu____3897
                   in
                match_args [] args argpats))
          | uu____3906 ->
              let uu____3911 =
                let uu____3912 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3913 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3914 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3912 uu____3913 uu____3914
                 in
              failwith uu____3911
           in
        aux p exp
  
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
    let pat_as_arg uu____3957 =
      match uu____3957 with
      | (p,i) ->
          let uu____3974 = decorated_pattern_as_term p  in
          (match uu____3974 with
           | (vars,te) ->
               let uu____3997 =
                 let uu____4002 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____4002)  in
               (vars, uu____3997))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____4016 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____4016)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____4020 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4020)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____4024 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4024)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____4045 =
          let uu____4062 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____4062 FStar_List.unzip  in
        (match uu____4045 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____4182 =
               let uu____4183 =
                 let uu____4184 =
                   let uu____4199 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____4199, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____4184  in
               mk1 uu____4183  in
             (vars1, uu____4182))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____4235,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____4245,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____4259 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____4281)::[] -> wp
      | uu____4298 ->
          let uu____4307 =
            let uu____4308 =
              let uu____4309 =
                FStar_List.map
                  (fun uu____4319  ->
                     match uu____4319 with
                     | (x,uu____4325) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4309 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4308
             in
          failwith uu____4307
       in
    let uu____4328 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4328, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4344 = destruct_comp c  in
        match uu____4344 with
        | (u,uu____4352,wp) ->
            let uu____4354 =
              let uu____4363 =
                let uu____4370 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4370  in
              [uu____4363]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4354;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4398 =
          let uu____4405 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4406 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4405 uu____4406  in
        match uu____4398 with | (m,uu____4408,uu____4409) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4425 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4425
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
        let uu____4468 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4468 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4505 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4505 with
             | (a,kwp) ->
                 let uu____4536 = destruct_comp m1  in
                 let uu____4543 = destruct_comp m2  in
                 ((md, a, kwp), uu____4536, uu____4543))
  
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
            let uu____4623 =
              let uu____4624 =
                let uu____4633 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4633]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4624;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4623
  
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
          let uu____4709 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4709
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
      let uu____4721 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4721
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4724  ->
           let uu____4725 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4725)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4731 =
      let uu____4732 = FStar_Syntax_Subst.compress t  in
      uu____4732.FStar_Syntax_Syntax.n  in
    match uu____4731 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4735 -> true
    | uu____4748 -> false
  
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
              let uu____4805 =
                let uu____4806 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4806  in
              if uu____4805
              then f
              else (let uu____4808 = reason1 ()  in label uu____4808 r f)
  
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
            let uu___135_4825 = g  in
            let uu____4826 =
              let uu____4827 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4827  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4826;
              FStar_TypeChecker_Env.deferred =
                (uu___135_4825.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___135_4825.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___135_4825.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4847 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4847
        then c
        else
          (let uu____4849 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4849
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4908 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4908]  in
                       let us =
                         let uu____4924 =
                           let uu____4927 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4927]  in
                         u_res :: uu____4924  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4933 =
                         let uu____4938 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4939 =
                           let uu____4940 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4947 =
                             let uu____4956 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4963 =
                               let uu____4972 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4972]  in
                             uu____4956 :: uu____4963  in
                           uu____4940 :: uu____4947  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4938 uu____4939
                          in
                       uu____4933 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____5006 = destruct_comp c1  in
              match uu____5006 with
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
          (fun uu____5041  ->
             let uu____5042 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____5042)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___106_5051  ->
            match uu___106_5051 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____5052 -> false))
  
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
                (let uu____5074 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____5074))
               &&
               (let uu____5081 = FStar_Syntax_Util.head_and_args' e  in
                match uu____5081 with
                | (head1,uu____5095) ->
                    let uu____5112 =
                      let uu____5113 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5113.FStar_Syntax_Syntax.n  in
                    (match uu____5112 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____5117 =
                           let uu____5118 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____5118
                            in
                         Prims.op_Negation uu____5117
                     | uu____5119 -> true)))
              &&
              (let uu____5121 = should_not_inline_lc lc  in
               Prims.op_Negation uu____5121)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____5155 =
              let uu____5156 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____5156  in
            if uu____5155
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____5158 = FStar_Syntax_Util.is_unit t  in
               if uu____5158
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
                    let uu____5164 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____5164
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____5166 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____5166 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____5176 =
                             let uu____5177 =
                               let uu____5182 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____5183 =
                                 let uu____5184 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____5191 =
                                   let uu____5200 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____5200]  in
                                 uu____5184 :: uu____5191  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____5182
                                 uu____5183
                                in
                             uu____5177 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____5176)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____5228 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____5228
           then
             let uu____5229 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____5230 = FStar_Syntax_Print.term_to_string v1  in
             let uu____5231 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____5229 uu____5230 uu____5231
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____5244 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___107_5248  ->
              match uu___107_5248 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5249 -> false))
       in
    if uu____5244
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___108_5258  ->
              match uu___108_5258 with
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
        let uu____5277 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5277
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____5280 = destruct_comp c1  in
           match uu____5280 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____5294 =
                   let uu____5299 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____5300 =
                     let uu____5301 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____5308 =
                       let uu____5317 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____5324 =
                         let uu____5333 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____5333]  in
                       uu____5317 :: uu____5324  in
                     uu____5301 :: uu____5308  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____5299 uu____5300  in
                 uu____5294 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____5366 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____5366)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5389 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____5391 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____5391
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____5394 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____5394 weaken
  
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
               let uu____5437 = destruct_comp c1  in
               match uu____5437 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5451 =
                       let uu____5456 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5457 =
                         let uu____5458 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5465 =
                           let uu____5474 =
                             let uu____5481 =
                               let uu____5482 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5482 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5481
                              in
                           let uu____5489 =
                             let uu____5498 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5498]  in
                           uu____5474 :: uu____5489  in
                         uu____5458 :: uu____5465  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5456 uu____5457
                        in
                     uu____5451 FStar_Pervasives_Native.None
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
      fun e_for_debug_only  ->
        fun lc  ->
          fun g0  ->
            let uu____5573 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____5573
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5582 =
                   let uu____5589 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5589
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5582 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____5609 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___109_5617  ->
                               match uu___109_5617 with
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
                               | uu____5620 -> []))
                        in
                     FStar_List.append flags1 uu____5609
                  in
               let strengthen uu____5626 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____5630 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____5630 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____5633 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5633
                          then
                            let uu____5634 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____5635 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____5634 uu____5635
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____5637 =
                 let uu____5638 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____5638
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____5637,
                 (let uu___136_5640 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___136_5640.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___136_5640.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___136_5640.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___110_5647  ->
            match uu___110_5647 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5648 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____5675 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5675
          then e
          else
            (let uu____5679 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5681 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5681)
                in
             if uu____5679
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
          fun uu____5731  ->
            match uu____5731 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5751 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5751 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5759 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5759
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____5766 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____5766
                       then
                         let uu____5769 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____5769
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5773 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____5773
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5778 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____5778
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5782 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5782
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5791 =
                  let uu____5792 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5792
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
                       (fun uu____5806  ->
                          let uu____5807 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5808 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5810 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5807 uu____5808 uu____5810);
                     (let aux uu____5824 =
                        let uu____5825 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5825
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5846 ->
                              let uu____5847 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5847
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5866 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5866
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5937 =
                              let uu____5942 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5942, reason)  in
                            FStar_Util.Inl uu____5937
                        | uu____5949 -> aux ()  in
                      let try_simplify uu____5973 =
                        let rec maybe_close t x c =
                          let uu____5990 =
                            let uu____5991 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5991.FStar_Syntax_Syntax.n  in
                          match uu____5990 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5995) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____6001 -> c  in
                        let uu____6002 =
                          let uu____6003 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____6003  in
                        if uu____6002
                        then
                          let uu____6014 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____6014
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____6028 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____6028))
                        else
                          (let uu____6038 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____6038
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____6048 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____6048
                              then
                                let uu____6057 =
                                  let uu____6062 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____6062, "both gtot")  in
                                FStar_Util.Inl uu____6057
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____6086 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____6088 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____6088)
                                        in
                                     if uu____6086
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___137_6101 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___137_6101.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___137_6101.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____6102 =
                                         let uu____6107 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____6107, "c1 Tot")  in
                                       FStar_Util.Inl uu____6102
                                     else aux ()
                                 | uu____6113 -> aux ())))
                         in
                      let uu____6122 = try_simplify ()  in
                      match uu____6122 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____6142  ->
                                let uu____6143 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____6143);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____6152  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____6173 = lift_and_destruct env c11 c21
                                 in
                              match uu____6173 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6226 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____6226]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____6240 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____6240]
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
                                    let uu____6267 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____6274 =
                                      let uu____6283 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____6290 =
                                        let uu____6299 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____6306 =
                                          let uu____6315 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____6322 =
                                            let uu____6331 =
                                              let uu____6338 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____6338
                                               in
                                            [uu____6331]  in
                                          uu____6315 :: uu____6322  in
                                        uu____6299 :: uu____6306  in
                                      uu____6283 :: uu____6290  in
                                    uu____6267 :: uu____6274  in
                                  let wp =
                                    let uu____6378 =
                                      let uu____6383 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____6383 wp_args
                                       in
                                    uu____6378 FStar_Pervasives_Native.None
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
                              let uu____6408 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____6408 with
                              | (m,uu____6416,lift2) ->
                                  let c23 =
                                    let uu____6419 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____6419
                                     in
                                  let uu____6420 = destruct_comp c12  in
                                  (match uu____6420 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____6434 =
                                           let uu____6439 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____6440 =
                                             let uu____6441 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6448 =
                                               let uu____6457 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6457]  in
                                             uu____6441 :: uu____6448  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6439 uu____6440
                                            in
                                         uu____6434
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
                            let uu____6488 = destruct_comp c1_typ  in
                            match uu____6488 with
                            | (u_res_t1,res_t1,uu____6497) ->
                                let uu____6498 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6498
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6501 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6501
                                   then
                                     (debug1
                                        (fun uu____6509  ->
                                           let uu____6510 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6511 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6510 uu____6511);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6516 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6518 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6518)
                                         in
                                      if uu____6516
                                      then
                                        let e1' =
                                          let uu____6538 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____6538
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____6547  ->
                                              let uu____6548 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____6549 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____6548 uu____6549);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____6561  ->
                                              let uu____6562 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____6563 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____6562 uu____6563);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6568 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6568
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
      | uu____6584 -> g2
  
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
            (let uu____6606 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____6606)
           in
        let flags1 =
          if should_return1
          then
            let uu____6612 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____6612
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____6624 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6628 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6628
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6632 =
              let uu____6633 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6633  in
            (if uu____6632
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___138_6638 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___138_6638.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___138_6638.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___138_6638.FStar_Syntax_Syntax.effect_args);
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
               let uu____6649 =
                 let uu____6650 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6650
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6649
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6653 =
               let uu____6654 =
                 let uu____6655 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6655
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____6654  in
             FStar_Syntax_Util.comp_set_flags uu____6653 flags1)
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
            fun uu____6690  ->
              match uu____6690 with
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
                    let uu____6702 =
                      ((let uu____6705 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6705) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6702
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6719 =
        let uu____6720 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6720  in
      FStar_Syntax_Syntax.fvar uu____6719 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6786  ->
                 match uu____6786 with
                 | (uu____6799,eff_label,uu____6801,uu____6802) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6813 =
          let uu____6820 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6854  ->
                    match uu____6854 with
                    | (uu____6867,uu____6868,flags1,uu____6870) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___111_6884  ->
                                match uu___111_6884 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6885 -> false))))
             in
          if uu____6820
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6813 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6908 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6910 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6910
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6948 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6949 =
                     let uu____6954 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____6955 =
                       let uu____6956 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____6963 =
                         let uu____6972 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____6979 =
                           let uu____6988 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____6995 =
                             let uu____7004 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____7004]  in
                           uu____6988 :: uu____6995  in
                         uu____6972 :: uu____6979  in
                       uu____6956 :: uu____6963  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6954 uu____6955  in
                   uu____6949 FStar_Pervasives_Native.None uu____6948  in
                 let default_case =
                   let post_k =
                     let uu____7047 =
                       let uu____7054 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7054]  in
                     let uu____7067 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7047 uu____7067  in
                   let kwp =
                     let uu____7073 =
                       let uu____7080 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7080]  in
                     let uu____7093 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7073 uu____7093  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7100 =
                       let uu____7101 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7101]  in
                     let uu____7114 =
                       let uu____7117 =
                         let uu____7124 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7124
                          in
                       let uu____7125 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7117 uu____7125  in
                     FStar_Syntax_Util.abs uu____7100 uu____7114
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
                   let uu____7147 =
                     should_not_inline_whole_match ||
                       (let uu____7149 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7149)
                      in
                   if uu____7147 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____7182  ->
                        fun celse  ->
                          match uu____7182 with
                          | (g,eff_label,uu____7198,cthen) ->
                              let uu____7210 =
                                let uu____7235 =
                                  let uu____7236 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____7236
                                   in
                                lift_and_destruct env uu____7235 celse  in
                              (match uu____7210 with
                               | ((md,uu____7238,uu____7239),(uu____7240,uu____7241,wp_then),
                                  (uu____7243,uu____7244,wp_else)) ->
                                   let uu____7264 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____7264 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____7278::[] -> comp
                 | uu____7318 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____7336 = destruct_comp comp1  in
                     (match uu____7336 with
                      | (uu____7343,uu____7344,wp) ->
                          let wp1 =
                            let uu____7349 =
                              let uu____7354 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____7355 =
                                let uu____7356 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____7363 =
                                  let uu____7372 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____7372]  in
                                uu____7356 :: uu____7363  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____7354
                                uu____7355
                               in
                            uu____7349 FStar_Pervasives_Native.None
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
          let uu____7431 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7431 with
          | FStar_Pervasives_Native.None  ->
              let uu____7440 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____7445 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____7440 uu____7445
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
          let is_type1 t1 =
            let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
            let uu____7488 =
              let uu____7489 = FStar_Syntax_Subst.compress t2  in
              uu____7489.FStar_Syntax_Syntax.n  in
            match uu____7488 with
            | FStar_Syntax_Syntax.Tm_type uu____7492 -> true
            | uu____7493 -> false  in
          let uu____7494 =
            let uu____7495 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____7495.FStar_Syntax_Syntax.n  in
          match uu____7494 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____7503 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____7513 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____7513
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____7515 =
                  let uu____7516 =
                    let uu____7517 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____7517
                     in
                  (FStar_Pervasives_Native.None, uu____7516)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____7515
                 in
              let e1 =
                let uu____7523 =
                  let uu____7528 =
                    let uu____7529 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____7529]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7528  in
                uu____7523 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____7550 -> (e, lc)
  
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
          let use_eq =
            env.FStar_TypeChecker_Env.use_eq ||
              (let uu____7587 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____7587 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____7610 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____7632 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____7632, false)
            else
              (let uu____7638 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____7638, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____7649) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____7658 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____7658 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___139_7672 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___139_7672.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___139_7672.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___139_7672.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____7677 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____7677 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___140_7685 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___140_7685.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___140_7685.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___140_7685.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___141_7688 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_7688.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_7688.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___141_7688.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____7694 =
                     let uu____7695 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____7695
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____7698 =
                          let uu____7699 = FStar_Syntax_Subst.compress f1  in
                          uu____7699.FStar_Syntax_Syntax.n  in
                        match uu____7698 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____7702,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____7704;
                                          FStar_Syntax_Syntax.vars =
                                            uu____7705;_},uu____7706)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___142_7728 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___142_7728.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___142_7728.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___142_7728.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____7729 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____7732 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7732
                              then
                                let uu____7733 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____7734 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____7735 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____7736 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____7733 uu____7734 uu____7735 uu____7736
                              else ());
                             (let u_t_opt = comp_univ_opt c  in
                              let x =
                                FStar_Syntax_Syntax.new_bv
                                  (FStar_Pervasives_Native.Some
                                     (t.FStar_Syntax_Syntax.pos)) t
                                 in
                              let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                              let cret = return_value env u_t_opt t xexp  in
                              let guard =
                                if apply_guard1
                                then
                                  let uu____7745 =
                                    let uu____7750 =
                                      let uu____7751 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____7751]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____7750
                                     in
                                  uu____7745 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____7773 =
                                let uu____7778 =
                                  FStar_All.pipe_left
                                    (fun _0_17  ->
                                       FStar_Pervasives_Native.Some _0_17)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____7795 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____7796 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____7797 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____7778 uu____7795
                                  e uu____7796 uu____7797
                                 in
                              match uu____7773 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___143_7801 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___143_7801.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___143_7801.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____7803 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____7803
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____7808 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7808
                                    then
                                      let uu____7809 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____7809
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___112_7819  ->
                             match uu___112_7819 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____7822 -> []))
                      in
                   let lc1 =
                     let uu____7824 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____7824 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___144_7826 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___144_7826.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___144_7826.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___144_7826.FStar_TypeChecker_Env.implicits)
                     }  in
                   (e, lc1, g2))
  
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
        let uu____7861 =
          let uu____7864 =
            let uu____7869 =
              let uu____7870 =
                let uu____7877 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7877  in
              [uu____7870]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7869  in
          uu____7864 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7861  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____7898 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7898
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7914 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7929 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7945 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7945
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7959)::(ens,uu____7961)::uu____7962 ->
                    let uu____7991 =
                      let uu____7994 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7994  in
                    let uu____7995 =
                      let uu____7996 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7996  in
                    (uu____7991, uu____7995)
                | uu____7999 ->
                    let uu____8008 =
                      let uu____8013 =
                        let uu____8014 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8014
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8013)
                       in
                    FStar_Errors.raise_error uu____8008
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8030)::uu____8031 ->
                    let uu____8050 =
                      let uu____8055 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8055
                       in
                    (match uu____8050 with
                     | (us_r,uu____8087) ->
                         let uu____8088 =
                           let uu____8093 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8093
                            in
                         (match uu____8088 with
                          | (us_e,uu____8125) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8128 =
                                  let uu____8129 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8129
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8128
                                  us_r
                                 in
                              let as_ens =
                                let uu____8131 =
                                  let uu____8132 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8132
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8131
                                  us_e
                                 in
                              let req =
                                let uu____8136 =
                                  let uu____8141 =
                                    let uu____8142 =
                                      let uu____8151 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8151]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8142
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8141
                                   in
                                uu____8136 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8183 =
                                  let uu____8188 =
                                    let uu____8189 =
                                      let uu____8198 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8198]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8189
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8188
                                   in
                                uu____8183 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8227 =
                                let uu____8230 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8230  in
                              let uu____8231 =
                                let uu____8232 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8232  in
                              (uu____8227, uu____8231)))
                | uu____8235 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
         in
      (let uu____8265 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8265
       then
         let uu____8266 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8267 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8266 uu____8267
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
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Reify;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
           in
        (let uu____8311 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8311
         then
           let uu____8312 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8313 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8312
             uu____8313
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8320 =
      let uu____8321 =
        let uu____8322 = FStar_Syntax_Subst.compress t  in
        uu____8322.FStar_Syntax_Syntax.n  in
      match uu____8321 with
      | FStar_Syntax_Syntax.Tm_app uu____8325 -> false
      | uu____8340 -> true  in
    if uu____8320
    then t
    else
      (let uu____8342 = FStar_Syntax_Util.head_and_args t  in
       match uu____8342 with
       | (head1,args) ->
           let uu____8379 =
             let uu____8380 =
               let uu____8381 = FStar_Syntax_Subst.compress head1  in
               uu____8381.FStar_Syntax_Syntax.n  in
             match uu____8380 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8384 -> false  in
           if uu____8379
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8406 ->
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
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard)
        else
          (let number_of_implicits t1 =
             let uu____8451 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____8451 with
             | (formals,uu____8465) ->
                 let n_implicits =
                   let uu____8483 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____8561  ->
                             match uu____8561 with
                             | (uu____8568,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____8483 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____8701 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____8701 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____8725 =
                     let uu____8730 =
                       let uu____8731 = FStar_Util.string_of_int n_expected
                          in
                       let uu____8738 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____8739 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____8731 uu____8738 uu____8739
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____8730)
                      in
                   let uu____8746 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____8725 uu____8746
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___113_8769 =
             match uu___113_8769 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____8799 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____8799 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_18,uu____8914) when
                          _0_18 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____8957,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____8990 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____8990 with
                           | (v1,uu____9030,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____9049 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____9049 with
                                | (args,bs3,subst3,g') ->
                                    let uu____9142 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____9142)))
                      | (uu____9169,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____9215 =
                      let uu____9242 = inst_n_binders t  in
                      aux [] uu____9242 bs1  in
                    (match uu____9215 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____9313) -> (e, torig, guard)
                          | (uu____9344,[]) when
                              let uu____9375 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____9375 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____9376 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____9404 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____9417 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9427 =
      let uu____9430 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9430
        (FStar_List.map
           (fun u  ->
              let uu____9440 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9440 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9427 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9461 = FStar_Util.set_is_empty x  in
      if uu____9461
      then []
      else
        (let s =
           let uu____9476 =
             let uu____9479 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9479  in
           FStar_All.pipe_right uu____9476 FStar_Util.set_elements  in
         (let uu____9495 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9495
          then
            let uu____9496 =
              let uu____9497 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9497  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9496
          else ());
         (let r =
            let uu____9504 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9504  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9543 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9543
                     then
                       let uu____9544 =
                         let uu____9545 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9545
                          in
                       let uu____9546 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9547 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9544 uu____9546 uu____9547
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
        let uu____9573 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9573 FStar_Util.set_elements  in
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
        | ([],uu____9611) -> generalized_univ_names
        | (uu____9618,[]) -> explicit_univ_names
        | uu____9625 ->
            let uu____9634 =
              let uu____9639 =
                let uu____9640 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9640
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9639)
               in
            FStar_Errors.raise_error uu____9634 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____9658 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____9658
       then
         let uu____9659 = FStar_Syntax_Print.term_to_string t  in
         let uu____9660 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____9659 uu____9660
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____9666 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____9666
        then
          let uu____9667 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____9667
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____9673 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____9673
         then
           let uu____9674 = FStar_Syntax_Print.term_to_string t  in
           let uu____9675 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____9674 uu____9675
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
        let uu____9753 =
          let uu____9754 =
            FStar_Util.for_all
              (fun uu____9767  ->
                 match uu____9767 with
                 | (uu____9776,uu____9777,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____9754  in
        if uu____9753
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____9825 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____9825
              then
                let uu____9826 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____9826
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____9830 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____9830
               then
                 let uu____9831 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____9831
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____9846 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____9846 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____9882 =
             match uu____9882 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____9926 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9926
                   then
                     let uu____9927 =
                       let uu____9928 =
                         let uu____9931 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____9931
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9928
                         (FStar_String.concat ", ")
                        in
                     let uu____9974 =
                       let uu____9975 =
                         let uu____9978 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____9978
                           (FStar_List.map
                              (fun u  ->
                                 let uu____9989 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____9990 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____9989
                                   uu____9990))
                          in
                       FStar_All.pipe_right uu____9975
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9927
                       uu____9974
                   else ());
                  (let univs2 =
                     let uu____9997 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10009 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10009) univs1
                       uu____9997
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10016 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10016
                    then
                      let uu____10017 =
                        let uu____10018 =
                          let uu____10021 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10021
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10018
                          (FStar_String.concat ", ")
                         in
                      let uu____10064 =
                        let uu____10065 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10076 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10077 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10076
                                    uu____10077))
                           in
                        FStar_All.pipe_right uu____10065
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10017 uu____10064
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10091 =
             let uu____10108 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10108  in
           match uu____10091 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10200 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10200
                 then ()
                 else
                   (let uu____10202 = lec_hd  in
                    match uu____10202 with
                    | (lb1,uu____10210,uu____10211) ->
                        let uu____10212 = lec2  in
                        (match uu____10212 with
                         | (lb2,uu____10220,uu____10221) ->
                             let msg =
                               let uu____10223 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10224 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10223 uu____10224
                                in
                             let uu____10225 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10225))
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
                 let uu____10289 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10289
                 then ()
                 else
                   (let uu____10291 = lec_hd  in
                    match uu____10291 with
                    | (lb1,uu____10299,uu____10300) ->
                        let uu____10301 = lec2  in
                        (match uu____10301 with
                         | (lb2,uu____10309,uu____10310) ->
                             let msg =
                               let uu____10312 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10313 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10312 uu____10313
                                in
                             let uu____10314 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10314))
                  in
               let lecs1 =
                 let uu____10324 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10383 = univs_and_uvars_of_lec this_lec  in
                        match uu____10383 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10324 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10484 = lec_hd  in
                   match uu____10484 with
                   | (lbname,e,c) ->
                       let uu____10494 =
                         let uu____10499 =
                           let uu____10500 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10501 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10502 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10500 uu____10501 uu____10502
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10499)
                          in
                       let uu____10503 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10494 uu____10503
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10524 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10524 with
                         | FStar_Pervasives_Native.Some uu____10533 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10540 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10544 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10544 with
                              | (bs,kres) ->
                                  ((let uu____10582 =
                                      let uu____10583 =
                                        let uu____10586 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____10586
                                         in
                                      uu____10583.FStar_Syntax_Syntax.n  in
                                    match uu____10582 with
                                    | FStar_Syntax_Syntax.Tm_type uu____10587
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____10591 =
                                          let uu____10592 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____10592  in
                                        if uu____10591
                                        then fail1 kres
                                        else ()
                                    | uu____10594 -> fail1 kres);
                                   (let a =
                                      let uu____10596 =
                                        let uu____10599 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_19  ->
                                             FStar_Pervasives_Native.Some
                                               _0_19) uu____10599
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____10596
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____10607 ->
                                          let uu____10614 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____10614
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
                      (fun uu____10725  ->
                         match uu____10725 with
                         | (lbname,e,c) ->
                             let uu____10779 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____10854 ->
                                   let uu____10869 = (e, c)  in
                                   (match uu____10869 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta]
                                            env c
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
                                                (fun uu____10920  ->
                                                   match uu____10920 with
                                                   | (x,uu____10928) ->
                                                       let uu____10933 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____10933)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____10951 =
                                                let uu____10952 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____10952
                                                 in
                                              if uu____10951
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
                                          let uu____10958 =
                                            let uu____10959 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____10959.FStar_Syntax_Syntax.n
                                             in
                                          match uu____10958 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10980 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____10980 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____10993 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____10997 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____10997, gen_tvars))
                                in
                             (match uu____10779 with
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
        (let uu____11151 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11151
         then
           let uu____11152 =
             let uu____11153 =
               FStar_List.map
                 (fun uu____11166  ->
                    match uu____11166 with
                    | (lb,uu____11174,uu____11175) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11153 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11152
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11196  ->
                match uu____11196 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11225 = gen env is_rec lecs  in
           match uu____11225 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11324  ->
                       match uu____11324 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11386 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11386
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11432  ->
                           match uu____11432 with
                           | (l,us,e,c,gvs) ->
                               let uu____11466 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11467 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11468 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11469 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11470 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11466 uu____11467 uu____11468
                                 uu____11469 uu____11470))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11511  ->
                match uu____11511 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11555 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11555, t, c, gvs)) univnames_lecs
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
              (let uu____11612 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11612 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11618 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____11618)
             in
          let is_var e1 =
            let uu____11627 =
              let uu____11628 = FStar_Syntax_Subst.compress e1  in
              uu____11628.FStar_Syntax_Syntax.n  in
            match uu____11627 with
            | FStar_Syntax_Syntax.Tm_name uu____11631 -> true
            | uu____11632 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___145_11652 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___145_11652.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___145_11652.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____11653 -> e2  in
          let env2 =
            let uu___146_11655 = env1  in
            let uu____11656 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_11655.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_11655.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_11655.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_11655.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___146_11655.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_11655.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_11655.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_11655.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_11655.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_11655.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_11655.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_11655.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_11655.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_11655.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_11655.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_11655.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____11656;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_11655.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_11655.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_11655.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_11655.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___146_11655.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___146_11655.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___146_11655.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___146_11655.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_11655.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___146_11655.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_11655.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___146_11655.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___146_11655.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___146_11655.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___146_11655.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___146_11655.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___146_11655.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___146_11655.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___146_11655.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___146_11655.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___146_11655.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____11657 = check1 env2 t1 t2  in
          match uu____11657 with
          | FStar_Pervasives_Native.None  ->
              let uu____11664 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____11669 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____11664 uu____11669
          | FStar_Pervasives_Native.Some g ->
              ((let uu____11676 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____11676
                then
                  let uu____11677 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____11677
                else ());
               (let uu____11679 = decorate e t2  in (uu____11679, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g1 =
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          FStar_Syntax_Util.is_pure_lcomp lc  in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
        let uu____11711 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____11711
        then
          let uu____11716 = discharge g1  in
          let uu____11717 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____11716, uu____11717)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____11724 =
               let uu____11725 =
                 let uu____11726 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____11726 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____11725
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____11724
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____11728 = destruct_comp c1  in
           match uu____11728 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____11745 = FStar_TypeChecker_Env.get_range env  in
                 let uu____11746 =
                   let uu____11751 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____11752 =
                     let uu____11753 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____11760 =
                       let uu____11769 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____11769]  in
                     uu____11753 :: uu____11760  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____11751 uu____11752  in
                 uu____11746 FStar_Pervasives_Native.None uu____11745  in
               ((let uu____11797 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____11797
                 then
                   let uu____11798 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____11798
                 else ());
                (let g2 =
                   let uu____11801 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____11801  in
                 let uu____11802 = discharge g2  in
                 let uu____11803 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____11802, uu____11803))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___114_11835 =
        match uu___114_11835 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____11843)::[] -> f fst1
        | uu____11860 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____11871 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____11871
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_or_e e =
        let uu____11882 =
          let uu____11883 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____11883  in
        FStar_All.pipe_right uu____11882
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_or_t t =
        let uu____11902 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____11902
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
         in
      let short_op_ite uu___115_11916 =
        match uu___115_11916 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11924)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11943)::[] ->
            let uu____11972 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____11972
              (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
        | uu____11973 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____11984 =
          let uu____11992 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____11992)  in
        let uu____12000 =
          let uu____12010 =
            let uu____12018 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12018)  in
          let uu____12026 =
            let uu____12036 =
              let uu____12044 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12044)  in
            let uu____12052 =
              let uu____12062 =
                let uu____12070 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12070)  in
              let uu____12078 =
                let uu____12088 =
                  let uu____12096 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12096)  in
                [uu____12088; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12062 :: uu____12078  in
            uu____12036 :: uu____12052  in
          uu____12010 :: uu____12026  in
        uu____11984 :: uu____12000  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12158 =
            FStar_Util.find_map table
              (fun uu____12173  ->
                 match uu____12173 with
                 | (x,mk1) ->
                     let uu____12190 = FStar_Ident.lid_equals x lid  in
                     if uu____12190
                     then
                       let uu____12193 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12193
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12158 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12196 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12202 =
      let uu____12203 = FStar_Syntax_Util.un_uinst l  in
      uu____12203.FStar_Syntax_Syntax.n  in
    match uu____12202 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12207 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12237)::uu____12238 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12249 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12256,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12257))::uu____12258 -> bs
      | uu____12269 ->
          let uu____12270 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12270 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12274 =
                 let uu____12275 = FStar_Syntax_Subst.compress t  in
                 uu____12275.FStar_Syntax_Syntax.n  in
               (match uu____12274 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12279) ->
                    let uu____12296 =
                      FStar_Util.prefix_until
                        (fun uu___116_12336  ->
                           match uu___116_12336 with
                           | (uu____12343,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____12344)) ->
                               false
                           | uu____12347 -> true) bs'
                       in
                    (match uu____12296 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____12382,uu____12383) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12455,uu____12456) ->
                         let uu____12529 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____12547  ->
                                   match uu____12547 with
                                   | (x,uu____12555) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____12529
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____12598  ->
                                     match uu____12598 with
                                     | (x,i) ->
                                         let uu____12617 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____12617, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12625 -> bs))
  
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
            let uu____12653 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12653
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
          let uu____12680 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____12680
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
        (let uu____12715 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____12715
         then
           ((let uu____12717 = FStar_Ident.text_of_lid lident  in
             d uu____12717);
            (let uu____12718 = FStar_Ident.text_of_lid lident  in
             let uu____12719 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____12718 uu____12719))
         else ());
        (let fv =
           let uu____12722 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____12722
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
         let uu____12732 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___147_12734 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___147_12734.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___147_12734.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___147_12734.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___147_12734.FStar_Syntax_Syntax.sigattrs)
           }), uu____12732))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___117_12750 =
        match uu___117_12750 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12751 -> false  in
      let reducibility uu___118_12757 =
        match uu___118_12757 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____12758 -> false  in
      let assumption uu___119_12764 =
        match uu___119_12764 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____12765 -> false  in
      let reification uu___120_12771 =
        match uu___120_12771 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____12772 -> true
        | uu____12773 -> false  in
      let inferred uu___121_12779 =
        match uu___121_12779 with
        | FStar_Syntax_Syntax.Discriminator uu____12780 -> true
        | FStar_Syntax_Syntax.Projector uu____12781 -> true
        | FStar_Syntax_Syntax.RecordType uu____12786 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____12795 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____12804 -> false  in
      let has_eq uu___122_12810 =
        match uu___122_12810 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____12811 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____12875 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12880 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____12884 =
        let uu____12885 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___123_12889  ->
                  match uu___123_12889 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____12890 -> false))
           in
        FStar_All.pipe_right uu____12885 Prims.op_Negation  in
      if uu____12884
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____12905 =
            let uu____12910 =
              let uu____12911 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____12911 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____12910)  in
          FStar_Errors.raise_error uu____12905 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____12923 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____12927 =
            let uu____12928 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____12928  in
          if uu____12927 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____12933),uu____12934) ->
              ((let uu____12944 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____12944
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____12948 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____12948
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____12954 ->
              let uu____12963 =
                let uu____12964 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____12964  in
              if uu____12963 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____12970 ->
              let uu____12977 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____12977 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____12981 ->
              let uu____12988 =
                let uu____12989 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____12989  in
              if uu____12988 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12995 ->
              let uu____12996 =
                let uu____12997 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12997  in
              if uu____12996 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13003 ->
              let uu____13004 =
                let uu____13005 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13005  in
              if uu____13004 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13011 ->
              let uu____13024 =
                let uu____13025 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13025  in
              if uu____13024 then err'1 () else ()
          | uu____13031 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____13065 =
          let uu____13066 = FStar_Syntax_Subst.compress t1  in
          uu____13066.FStar_Syntax_Syntax.n  in
        match uu____13065 with
        | FStar_Syntax_Syntax.Tm_type uu____13069 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____13072 =
                 let uu____13077 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____13077
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____13072
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____13095 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____13095
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____13112 =
                                 let uu____13113 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____13113.FStar_Syntax_Syntax.n  in
                               match uu____13112 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____13117 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____13118 ->
            let uu____13131 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13131 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____13157 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____13157
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____13159;
               FStar_Syntax_Syntax.index = uu____13160;
               FStar_Syntax_Syntax.sort = t2;_},uu____13162)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13170,uu____13171) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____13213::[]) ->
            let uu____13244 =
              let uu____13245 = FStar_Syntax_Util.un_uinst head1  in
              uu____13245.FStar_Syntax_Syntax.n  in
            (match uu____13244 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____13249 -> false)
        | uu____13250 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Primops;
            FStar_TypeChecker_Normalize.Weak;
            FStar_TypeChecker_Normalize.HNF;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.delta_constant;
            FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Iota] env t1
           in
        let res = aux_whnf env t2  in
        (let uu____13258 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____13258
         then
           let uu____13259 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____13259
         else ());
        res
       in aux g t
  