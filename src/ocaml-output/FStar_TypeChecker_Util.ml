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
                     let uu___98_241 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___98_241.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___98_241.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___98_241.FStar_TypeChecker_Env.univ_ineqs);
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
                         (fun uu___79_420  ->
                            match uu___79_420 with
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
                  (let uu___99_745 = g  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___99_745.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = solve_now;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___99_745.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___99_745.FStar_TypeChecker_Env.implicits)
                   })
                 in
              let g2 =
                let uu___100_747 = g1  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___100_747.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred = defer;
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___100_747.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits =
                    (uu___100_747.FStar_TypeChecker_Env.implicits)
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
                 let uu___101_855 = g2  in
                 {
                   FStar_TypeChecker_Env.guard_f =
                     (uu___101_855.FStar_TypeChecker_Env.guard_f);
                   FStar_TypeChecker_Env.deferred =
                     (uu___101_855.FStar_TypeChecker_Env.deferred);
                   FStar_TypeChecker_Env.univ_ineqs =
                     (uu___101_855.FStar_TypeChecker_Env.univ_ineqs);
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
                ((let uu___102_1293 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___102_1293.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___102_1293.FStar_Syntax_Syntax.index);
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
                            let uu___103_1458 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___103_1458.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___103_1458.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____1459 =
                            let uu____1472 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            new_implicit_var "" uu____1472 env1 t  in
                          (match uu____1459 with
                           | (e,uu____1494,g') ->
                               let p2 =
                                 let uu___104_1511 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___104_1511.FStar_Syntax_Syntax.p)
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
                       (fun uu____1762  ->
                          fun uu____1763  ->
                            match (uu____1762, uu____1763) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1961 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1961 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____2037 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____2037, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1616 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____2180 =
                         let uu____2185 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____2186 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2185 uu____2186
                          in
                       uu____2180 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____2203 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____2214 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____2225 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____2203, uu____2214, uu____2225, env2, e, guard,
                       (let uu___105_2243 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___105_2243.FStar_Syntax_Syntax.p)
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
                    (fun uu____2343  ->
                       match uu____2343 with
                       | (p2,imp) ->
                           let uu____2362 = elaborate_pat env1 p2  in
                           (uu____2362, imp)) pats
                   in
                let uu____2367 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2367 with
                 | (uu____2374,t) ->
                     let uu____2376 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2376 with
                      | (f,uu____2392) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2518::uu____2519) ->
                                let uu____2562 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2562
                            | (uu____2571::uu____2572,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2650  ->
                                        match uu____2650 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2677 =
                                                     let uu____2680 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2680
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2677
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2682 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2682, true)
                                             | uu____2687 ->
                                                 let uu____2690 =
                                                   let uu____2695 =
                                                     let uu____2696 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2696
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2695)
                                                    in
                                                 let uu____2697 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2690 uu____2697)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2771,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2772)) when p_imp ->
                                     let uu____2775 = aux formals' pats'  in
                                     (p2, true) :: uu____2775
                                 | (uu____2792,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2800 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2800
                                        in
                                     let uu____2801 = aux formals' pats2  in
                                     (p3, true) :: uu____2801
                                 | (uu____2818,imp) ->
                                     let uu____2824 =
                                       let uu____2831 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2831)  in
                                     let uu____2834 = aux formals' pats'  in
                                     uu____2824 :: uu____2834)
                             in
                          let uu___106_2849 = p1  in
                          let uu____2852 =
                            let uu____2853 =
                              let uu____2866 = aux f pats1  in
                              (fv, uu____2866)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2853  in
                          {
                            FStar_Syntax_Syntax.v = uu____2852;
                            FStar_Syntax_Syntax.p =
                              (uu___106_2849.FStar_Syntax_Syntax.p)
                          }))
            | uu____2883 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2925 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2925 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2983 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2983 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____3009 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____3009
                       p3.FStar_Syntax_Syntax.p
                 | uu____3032 -> (b, a, w, arg, guard, p3))
             in
          let uu____3041 = one_pat true env p  in
          match uu____3041 with
          | (b,uu____3071,uu____3072,tm,guard,p1) -> (b, tm, guard, p1)
  
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
          | (uu____3134,FStar_Syntax_Syntax.Tm_uinst (e2,uu____3136)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____3141,uu____3142) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____3146 =
                    let uu____3147 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3148 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3147 uu____3148
                     in
                  failwith uu____3146)
               else ();
               (let uu____3151 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____3151
                then
                  let uu____3152 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____3153 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____3152
                    uu____3153
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___107_3157 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___107_3157.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___107_3157.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____3161 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____3161
                then
                  let uu____3162 =
                    let uu____3163 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____3164 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____3163 uu____3164
                     in
                  failwith uu____3162
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___108_3168 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___108_3168.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___108_3168.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____3170),uu____3171) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____3195 =
                  let uu____3196 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____3196  in
                if uu____3195
                then
                  let uu____3197 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3197
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____3216;
                FStar_Syntax_Syntax.vars = uu____3217;_},args))
              ->
              ((let uu____3256 =
                  let uu____3257 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3257 Prims.op_Negation  in
                if uu____3256
                then
                  let uu____3258 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3258
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3396)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3471) ->
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
                       | ((e2,imp),uu____3508) ->
                           let pat =
                             let uu____3530 = aux argpat e2  in
                             let uu____3531 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3530, uu____3531)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3536 ->
                      let uu____3559 =
                        let uu____3560 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3561 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3560 uu____3561
                         in
                      failwith uu____3559
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3571;
                     FStar_Syntax_Syntax.vars = uu____3572;_},uu____3573);
                FStar_Syntax_Syntax.pos = uu____3574;
                FStar_Syntax_Syntax.vars = uu____3575;_},args))
              ->
              ((let uu____3618 =
                  let uu____3619 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3619 Prims.op_Negation  in
                if uu____3618
                then
                  let uu____3620 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3620
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3758)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3833) ->
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
                       | ((e2,imp),uu____3870) ->
                           let pat =
                             let uu____3892 = aux argpat e2  in
                             let uu____3893 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3892, uu____3893)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3898 ->
                      let uu____3921 =
                        let uu____3922 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3923 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3922 uu____3923
                         in
                      failwith uu____3921
                   in
                match_args [] args argpats))
          | uu____3930 ->
              let uu____3935 =
                let uu____3936 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3937 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3938 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3936 uu____3937 uu____3938
                 in
              failwith uu____3935
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
    let pat_as_arg uu____3981 =
      match uu____3981 with
      | (p,i) ->
          let uu____3998 = decorated_pattern_as_term p  in
          (match uu____3998 with
           | (vars,te) ->
               let uu____4021 =
                 let uu____4026 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____4026)  in
               (vars, uu____4021))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____4040 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____4040)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____4044 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4044)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____4048 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____4048)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____4069 =
          let uu____4086 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____4086 FStar_List.unzip  in
        (match uu____4069 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____4208 =
               let uu____4209 =
                 let uu____4210 =
                   let uu____4225 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____4225, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____4210  in
               mk1 uu____4209  in
             (vars1, uu____4208))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____4261,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____4271,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____4285 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____4307)::[] -> wp
      | uu____4324 ->
          let uu____4333 =
            let uu____4334 =
              let uu____4335 =
                FStar_List.map
                  (fun uu____4345  ->
                     match uu____4345 with
                     | (x,uu____4351) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4335 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4334
             in
          failwith uu____4333
       in
    let uu____4354 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4354, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4370 = destruct_comp c  in
        match uu____4370 with
        | (u,uu____4378,wp) ->
            let uu____4380 =
              let uu____4389 =
                let uu____4396 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4396  in
              [uu____4389]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4380;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4424 =
          let uu____4431 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4432 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4431 uu____4432  in
        match uu____4424 with | (m,uu____4434,uu____4435) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4451 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4451
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
        let uu____4494 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4494 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4531 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4531 with
             | (a,kwp) ->
                 let uu____4562 = destruct_comp m1  in
                 let uu____4569 = destruct_comp m2  in
                 ((md, a, kwp), uu____4562, uu____4569))
  
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
            let uu____4649 =
              let uu____4650 =
                let uu____4659 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4659]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4650;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4649
  
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
          let uu____4735 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4735
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
      let uu____4747 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4747
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4750  ->
           let uu____4751 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4751)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4757 =
      let uu____4758 = FStar_Syntax_Subst.compress t  in
      uu____4758.FStar_Syntax_Syntax.n  in
    match uu____4757 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4761 -> true
    | uu____4774 -> false
  
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
              let uu____4831 =
                let uu____4832 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4832  in
              if uu____4831
              then f
              else (let uu____4834 = reason1 ()  in label uu____4834 r f)
  
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
            let uu___109_4851 = g  in
            let uu____4852 =
              let uu____4853 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4853  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4852;
              FStar_TypeChecker_Env.deferred =
                (uu___109_4851.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___109_4851.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___109_4851.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4873 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4873
        then c
        else
          (let uu____4875 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4875
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4934 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4934]  in
                       let us =
                         let uu____4950 =
                           let uu____4953 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4953]  in
                         u_res :: uu____4950  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4959 =
                         let uu____4964 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4965 =
                           let uu____4966 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4973 =
                             let uu____4982 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4989 =
                               let uu____4998 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4998]  in
                             uu____4982 :: uu____4989  in
                           uu____4966 :: uu____4973  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4964 uu____4965
                          in
                       uu____4959 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____5032 = destruct_comp c1  in
              match uu____5032 with
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
          (fun uu____5067  ->
             let uu____5068 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____5068)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___80_5077  ->
            match uu___80_5077 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____5078 -> false))
  
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
                (let uu____5100 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____5100))
               &&
               (let uu____5107 = FStar_Syntax_Util.head_and_args' e  in
                match uu____5107 with
                | (head1,uu____5121) ->
                    let uu____5138 =
                      let uu____5139 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5139.FStar_Syntax_Syntax.n  in
                    (match uu____5138 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____5143 =
                           let uu____5144 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____5144
                            in
                         Prims.op_Negation uu____5143
                     | uu____5145 -> true)))
              &&
              (let uu____5147 = should_not_inline_lc lc  in
               Prims.op_Negation uu____5147)
  
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
            let uu____5181 =
              let uu____5182 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____5182  in
            if uu____5181
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____5184 = FStar_Syntax_Util.is_unit t  in
               if uu____5184
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
                    let uu____5190 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____5190
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____5192 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____5192 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____5202 =
                             let uu____5203 =
                               let uu____5208 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____5209 =
                                 let uu____5210 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____5217 =
                                   let uu____5226 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____5226]  in
                                 uu____5210 :: uu____5217  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____5208
                                 uu____5209
                                in
                             uu____5203 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____5202)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____5254 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____5254
           then
             let uu____5255 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____5256 = FStar_Syntax_Print.term_to_string v1  in
             let uu____5257 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____5255 uu____5256 uu____5257
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____5270 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___81_5274  ->
              match uu___81_5274 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5275 -> false))
       in
    if uu____5270
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___82_5284  ->
              match uu___82_5284 with
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
        let uu____5303 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5303
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____5306 = destruct_comp c1  in
           match uu____5306 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____5320 =
                   let uu____5325 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____5326 =
                     let uu____5327 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____5334 =
                       let uu____5343 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____5350 =
                         let uu____5359 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____5359]  in
                       uu____5343 :: uu____5350  in
                     uu____5327 :: uu____5334  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____5325 uu____5326  in
                 uu____5320 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____5392 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____5392)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5415 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____5417 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____5417
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____5420 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____5420 weaken
  
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
               let uu____5463 = destruct_comp c1  in
               match uu____5463 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5477 =
                       let uu____5482 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5483 =
                         let uu____5484 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5491 =
                           let uu____5500 =
                             let uu____5507 =
                               let uu____5508 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5508 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5507
                              in
                           let uu____5515 =
                             let uu____5524 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5524]  in
                           uu____5500 :: uu____5515  in
                         uu____5484 :: uu____5491  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5482 uu____5483
                        in
                     uu____5477 FStar_Pervasives_Native.None
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
            let uu____5599 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____5599
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5608 =
                   let uu____5615 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5615
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5608 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____5635 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___83_5643  ->
                               match uu___83_5643 with
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
                               | uu____5646 -> []))
                        in
                     FStar_List.append flags1 uu____5635
                  in
               let strengthen uu____5652 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____5656 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____5656 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____5659 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5659
                          then
                            let uu____5660 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____5661 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____5660 uu____5661
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____5663 =
                 let uu____5664 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____5664
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____5663,
                 (let uu___110_5666 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___110_5666.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___110_5666.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___110_5666.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___84_5673  ->
            match uu___84_5673 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5674 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____5701 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5701
          then e
          else
            (let uu____5705 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5707 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5707)
                in
             if uu____5705
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
          fun uu____5757  ->
            match uu____5757 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5777 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5777 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5785 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5785
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____5792 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____5792
                       then
                         let uu____5795 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____5795
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5799 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____5799
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5804 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____5804
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5808 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5808
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5817 =
                  let uu____5818 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5818
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
                       (fun uu____5832  ->
                          let uu____5833 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5834 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5836 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5833 uu____5834 uu____5836);
                     (let aux uu____5850 =
                        let uu____5851 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5851
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5872 ->
                              let uu____5873 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5873
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5892 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5892
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5963 =
                              let uu____5968 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5968, reason)  in
                            FStar_Util.Inl uu____5963
                        | uu____5975 -> aux ()  in
                      let try_simplify uu____5999 =
                        let rec maybe_close t x c =
                          let uu____6016 =
                            let uu____6017 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____6017.FStar_Syntax_Syntax.n  in
                          match uu____6016 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____6021) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____6027 -> c  in
                        let uu____6028 =
                          let uu____6029 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____6029  in
                        if uu____6028
                        then
                          let uu____6040 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____6040
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____6054 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____6054))
                        else
                          (let uu____6064 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____6064
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____6074 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____6074
                              then
                                let uu____6083 =
                                  let uu____6088 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____6088, "both gtot")  in
                                FStar_Util.Inl uu____6083
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____6112 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____6114 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____6114)
                                        in
                                     if uu____6112
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___111_6127 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___111_6127.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___111_6127.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____6128 =
                                         let uu____6133 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____6133, "c1 Tot")  in
                                       FStar_Util.Inl uu____6128
                                     else aux ()
                                 | uu____6139 -> aux ())))
                         in
                      let uu____6148 = try_simplify ()  in
                      match uu____6148 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____6168  ->
                                let uu____6169 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____6169);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____6178  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____6199 = lift_and_destruct env c11 c21
                                 in
                              match uu____6199 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6252 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____6252]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____6266 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____6266]
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
                                    let uu____6293 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____6300 =
                                      let uu____6309 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____6316 =
                                        let uu____6325 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____6332 =
                                          let uu____6341 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____6348 =
                                            let uu____6357 =
                                              let uu____6364 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____6364
                                               in
                                            [uu____6357]  in
                                          uu____6341 :: uu____6348  in
                                        uu____6325 :: uu____6332  in
                                      uu____6309 :: uu____6316  in
                                    uu____6293 :: uu____6300  in
                                  let wp =
                                    let uu____6404 =
                                      let uu____6409 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____6409 wp_args
                                       in
                                    uu____6404 FStar_Pervasives_Native.None
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
                              let uu____6434 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____6434 with
                              | (m,uu____6442,lift2) ->
                                  let c23 =
                                    let uu____6445 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____6445
                                     in
                                  let uu____6446 = destruct_comp c12  in
                                  (match uu____6446 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____6460 =
                                           let uu____6465 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____6466 =
                                             let uu____6467 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6474 =
                                               let uu____6483 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6483]  in
                                             uu____6467 :: uu____6474  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6465 uu____6466
                                            in
                                         uu____6460
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
                            let uu____6514 = destruct_comp c1_typ  in
                            match uu____6514 with
                            | (u_res_t1,res_t1,uu____6523) ->
                                let uu____6524 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6524
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6527 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6527
                                   then
                                     (debug1
                                        (fun uu____6535  ->
                                           let uu____6536 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6537 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6536 uu____6537);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6542 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6544 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6544)
                                         in
                                      if uu____6542
                                      then
                                        let e1' =
                                          let uu____6564 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____6564
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____6573  ->
                                              let uu____6574 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____6575 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____6574 uu____6575);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____6587  ->
                                              let uu____6588 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____6589 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____6588 uu____6589);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6594 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6594
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
      | uu____6610 -> g2
  
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
            (let uu____6632 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____6632)
           in
        let flags1 =
          if should_return1
          then
            let uu____6638 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____6638
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____6650 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6654 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6654
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6658 =
              let uu____6659 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6659  in
            (if uu____6658
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___112_6664 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___112_6664.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___112_6664.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___112_6664.FStar_Syntax_Syntax.effect_args);
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
               let uu____6675 =
                 let uu____6676 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6676
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6675
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6679 =
               let uu____6680 =
                 let uu____6681 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6681
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____6680  in
             FStar_Syntax_Util.comp_set_flags uu____6679 flags1)
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
            fun uu____6716  ->
              match uu____6716 with
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
                    let uu____6728 =
                      ((let uu____6731 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6731) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6728
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6745 =
        let uu____6746 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6746  in
      FStar_Syntax_Syntax.fvar uu____6745 FStar_Syntax_Syntax.Delta_constant
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
               fun uu____6812  ->
                 match uu____6812 with
                 | (uu____6825,eff_label,uu____6827,uu____6828) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6839 =
          let uu____6846 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6880  ->
                    match uu____6880 with
                    | (uu____6893,uu____6894,flags1,uu____6896) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___85_6910  ->
                                match uu___85_6910 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6911 -> false))))
             in
          if uu____6846
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6839 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6934 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6936 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6936
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6974 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6975 =
                     let uu____6980 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____6981 =
                       let uu____6982 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____6989 =
                         let uu____6998 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____7005 =
                           let uu____7014 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____7021 =
                             let uu____7030 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____7030]  in
                           uu____7014 :: uu____7021  in
                         uu____6998 :: uu____7005  in
                       uu____6982 :: uu____6989  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6980 uu____6981  in
                   uu____6975 FStar_Pervasives_Native.None uu____6974  in
                 let default_case =
                   let post_k =
                     let uu____7073 =
                       let uu____7080 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____7080]  in
                     let uu____7093 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7073 uu____7093  in
                   let kwp =
                     let uu____7099 =
                       let uu____7106 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____7106]  in
                     let uu____7119 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____7099 uu____7119  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____7126 =
                       let uu____7127 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____7127]  in
                     let uu____7140 =
                       let uu____7143 =
                         let uu____7150 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____7150
                          in
                       let uu____7151 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____7143 uu____7151  in
                     FStar_Syntax_Util.abs uu____7126 uu____7140
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
                   let uu____7173 =
                     should_not_inline_whole_match ||
                       (let uu____7175 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____7175)
                      in
                   if uu____7173 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____7208  ->
                        fun celse  ->
                          match uu____7208 with
                          | (g,eff_label,uu____7224,cthen) ->
                              let uu____7236 =
                                let uu____7261 =
                                  let uu____7262 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____7262
                                   in
                                lift_and_destruct env uu____7261 celse  in
                              (match uu____7236 with
                               | ((md,uu____7264,uu____7265),(uu____7266,uu____7267,wp_then),
                                  (uu____7269,uu____7270,wp_else)) ->
                                   let uu____7290 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____7290 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____7304::[] -> comp
                 | uu____7344 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____7362 = destruct_comp comp1  in
                     (match uu____7362 with
                      | (uu____7369,uu____7370,wp) ->
                          let wp1 =
                            let uu____7375 =
                              let uu____7380 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____7381 =
                                let uu____7382 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____7389 =
                                  let uu____7398 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____7398]  in
                                uu____7382 :: uu____7389  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____7380
                                uu____7381
                               in
                            uu____7375 FStar_Pervasives_Native.None
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
          let uu____7457 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7457 with
          | FStar_Pervasives_Native.None  ->
              let uu____7466 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____7471 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____7466 uu____7471
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
            let uu____7514 =
              let uu____7515 = FStar_Syntax_Subst.compress t2  in
              uu____7515.FStar_Syntax_Syntax.n  in
            match uu____7514 with
            | FStar_Syntax_Syntax.Tm_type uu____7518 -> true
            | uu____7519 -> false  in
          let uu____7520 =
            let uu____7521 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____7521.FStar_Syntax_Syntax.n  in
          match uu____7520 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____7529 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____7539 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____7539
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____7541 =
                  let uu____7542 =
                    let uu____7543 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____7543
                     in
                  (FStar_Pervasives_Native.None, uu____7542)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____7541
                 in
              let e1 =
                let uu____7549 =
                  let uu____7554 =
                    let uu____7555 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____7555]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7554  in
                uu____7549 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____7576 -> (e, lc)
  
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
              (let uu____7613 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____7613 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____7636 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____7658 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____7658, false)
            else
              (let uu____7664 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____7664, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____7675) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____7684 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____7684 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___113_7698 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___113_7698.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___113_7698.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___113_7698.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____7703 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____7703 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___114_7711 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___114_7711.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___114_7711.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___114_7711.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___115_7714 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___115_7714.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___115_7714.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___115_7714.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____7720 =
                     let uu____7721 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____7721
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____7724 =
                          let uu____7725 = FStar_Syntax_Subst.compress f1  in
                          uu____7725.FStar_Syntax_Syntax.n  in
                        match uu____7724 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____7728,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____7730;
                                          FStar_Syntax_Syntax.vars =
                                            uu____7731;_},uu____7732)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___116_7754 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___116_7754.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___116_7754.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___116_7754.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____7755 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____7758 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7758
                              then
                                let uu____7759 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____7760 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____7761 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____7762 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____7759 uu____7760 uu____7761 uu____7762
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
                                  let uu____7771 =
                                    let uu____7776 =
                                      let uu____7777 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____7777]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____7776
                                     in
                                  uu____7771 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____7799 =
                                let uu____7804 =
                                  FStar_All.pipe_left
                                    (fun _0_17  ->
                                       FStar_Pervasives_Native.Some _0_17)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____7821 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____7822 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____7823 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____7804 uu____7821
                                  e uu____7822 uu____7823
                                 in
                              match uu____7799 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___117_7827 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___117_7827.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___117_7827.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____7829 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____7829
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____7834 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7834
                                    then
                                      let uu____7835 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____7835
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___86_7845  ->
                             match uu___86_7845 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____7848 -> []))
                      in
                   let lc1 =
                     let uu____7850 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____7850 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___118_7852 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___118_7852.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___118_7852.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___118_7852.FStar_TypeChecker_Env.implicits)
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
        let uu____7887 =
          let uu____7890 =
            let uu____7895 =
              let uu____7896 =
                let uu____7903 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7903  in
              [uu____7896]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7895  in
          uu____7890 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7887  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____7924 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7924
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7940 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7955 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7971 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7971
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7985)::(ens,uu____7987)::uu____7988 ->
                    let uu____8017 =
                      let uu____8020 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____8020  in
                    let uu____8021 =
                      let uu____8022 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____8022  in
                    (uu____8017, uu____8021)
                | uu____8025 ->
                    let uu____8034 =
                      let uu____8039 =
                        let uu____8040 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____8040
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____8039)
                       in
                    FStar_Errors.raise_error uu____8034
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____8056)::uu____8057 ->
                    let uu____8076 =
                      let uu____8081 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____8081
                       in
                    (match uu____8076 with
                     | (us_r,uu____8113) ->
                         let uu____8114 =
                           let uu____8119 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____8119
                            in
                         (match uu____8114 with
                          | (us_e,uu____8151) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____8154 =
                                  let uu____8155 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8155
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8154
                                  us_r
                                 in
                              let as_ens =
                                let uu____8157 =
                                  let uu____8158 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____8158
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____8157
                                  us_e
                                 in
                              let req =
                                let uu____8162 =
                                  let uu____8167 =
                                    let uu____8168 =
                                      let uu____8177 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8177]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8168
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____8167
                                   in
                                uu____8162 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____8209 =
                                  let uu____8214 =
                                    let uu____8215 =
                                      let uu____8224 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8224]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____8215
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____8214
                                   in
                                uu____8209 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____8253 =
                                let uu____8256 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____8256  in
                              let uu____8257 =
                                let uu____8258 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____8258  in
                              (uu____8253, uu____8257)))
                | uu____8261 -> failwith "Impossible"))
  
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
      (let uu____8291 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____8291
       then
         let uu____8292 = FStar_Syntax_Print.term_to_string tm  in
         let uu____8293 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____8292 uu____8293
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
        (let uu____8337 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____8337
         then
           let uu____8338 = FStar_Syntax_Print.term_to_string tm  in
           let uu____8339 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____8338
             uu____8339
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____8346 =
      let uu____8347 =
        let uu____8348 = FStar_Syntax_Subst.compress t  in
        uu____8348.FStar_Syntax_Syntax.n  in
      match uu____8347 with
      | FStar_Syntax_Syntax.Tm_app uu____8351 -> false
      | uu____8366 -> true  in
    if uu____8346
    then t
    else
      (let uu____8368 = FStar_Syntax_Util.head_and_args t  in
       match uu____8368 with
       | (head1,args) ->
           let uu____8405 =
             let uu____8406 =
               let uu____8407 = FStar_Syntax_Subst.compress head1  in
               uu____8407.FStar_Syntax_Syntax.n  in
             match uu____8406 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____8410 -> false  in
           if uu____8405
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____8432 ->
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
             let uu____8477 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____8477 with
             | (formals,uu____8491) ->
                 let n_implicits =
                   let uu____8509 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____8587  ->
                             match uu____8587 with
                             | (uu____8594,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____8509 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____8727 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____8727 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____8751 =
                     let uu____8756 =
                       let uu____8757 = FStar_Util.string_of_int n_expected
                          in
                       let uu____8764 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____8765 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____8757 uu____8764 uu____8765
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____8756)
                      in
                   let uu____8772 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____8751 uu____8772
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___87_8795 =
             match uu___87_8795 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____8825 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____8825 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_18,uu____8940) when
                          _0_18 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____8983,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____9016 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____9016 with
                           | (v1,uu____9056,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____9075 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____9075 with
                                | (args,bs3,subst3,g') ->
                                    let uu____9168 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____9168)))
                      | (uu____9195,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____9241 =
                      let uu____9268 = inst_n_binders t  in
                      aux [] uu____9268 bs1  in
                    (match uu____9241 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____9339) -> (e, torig, guard)
                          | (uu____9370,[]) when
                              let uu____9401 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____9401 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____9402 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____9430 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____9443 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9453 =
      let uu____9456 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9456
        (FStar_List.map
           (fun u  ->
              let uu____9466 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9466 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9453 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9487 = FStar_Util.set_is_empty x  in
      if uu____9487
      then []
      else
        (let s =
           let uu____9502 =
             let uu____9513 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9513  in
           FStar_All.pipe_right uu____9502 FStar_Util.set_elements  in
         (let uu____9545 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9545
          then
            let uu____9546 =
              let uu____9547 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9547  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9546
          else ());
         (let r =
            let uu____9554 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9554  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9593 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9593
                     then
                       let uu____9594 =
                         let uu____9595 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9595
                          in
                       let uu____9596 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9597 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9594 uu____9596 uu____9597
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
        let uu____9623 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9623 FStar_Util.set_elements  in
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
        | ([],uu____9661) -> generalized_univ_names
        | (uu____9668,[]) -> explicit_univ_names
        | uu____9675 ->
            let uu____9684 =
              let uu____9689 =
                let uu____9690 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9690
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9689)
               in
            FStar_Errors.raise_error uu____9684 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____9708 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____9708
       then
         let uu____9709 = FStar_Syntax_Print.term_to_string t  in
         let uu____9710 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____9709 uu____9710
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____9716 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____9716
        then
          let uu____9717 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____9717
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____9723 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____9723
         then
           let uu____9724 = FStar_Syntax_Print.term_to_string t  in
           let uu____9725 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____9724 uu____9725
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
        let uu____9803 =
          let uu____9804 =
            FStar_Util.for_all
              (fun uu____9817  ->
                 match uu____9817 with
                 | (uu____9826,uu____9827,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____9804  in
        if uu____9803
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____9875 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____9875
              then
                let uu____9876 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____9876
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____9880 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____9880
               then
                 let uu____9881 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____9881
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____9896 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____9896 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____9932 =
             match uu____9932 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____9976 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9976
                   then
                     let uu____9977 =
                       let uu____9978 =
                         let uu____9981 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____9981
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9978
                         (FStar_String.concat ", ")
                        in
                     let uu____10024 =
                       let uu____10025 =
                         let uu____10028 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____10028
                           (FStar_List.map
                              (fun u  ->
                                 let uu____10039 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____10040 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____10039
                                   uu____10040))
                          in
                       FStar_All.pipe_right uu____10025
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9977
                       uu____10024
                   else ());
                  (let univs2 =
                     let uu____10047 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____10059 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____10059) univs1
                       uu____10047
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____10066 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____10066
                    then
                      let uu____10067 =
                        let uu____10068 =
                          let uu____10071 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____10071
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____10068
                          (FStar_String.concat ", ")
                         in
                      let uu____10114 =
                        let uu____10115 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____10126 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____10127 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____10126
                                    uu____10127))
                           in
                        FStar_All.pipe_right uu____10115
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____10067 uu____10114
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____10141 =
             let uu____10158 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____10158  in
           match uu____10141 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____10250 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____10250
                 then ()
                 else
                   (let uu____10252 = lec_hd  in
                    match uu____10252 with
                    | (lb1,uu____10260,uu____10261) ->
                        let uu____10262 = lec2  in
                        (match uu____10262 with
                         | (lb2,uu____10270,uu____10271) ->
                             let msg =
                               let uu____10273 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10274 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____10273 uu____10274
                                in
                             let uu____10275 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____10275))
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
                 let uu____10339 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____10339
                 then ()
                 else
                   (let uu____10341 = lec_hd  in
                    match uu____10341 with
                    | (lb1,uu____10349,uu____10350) ->
                        let uu____10351 = lec2  in
                        (match uu____10351 with
                         | (lb2,uu____10359,uu____10360) ->
                             let msg =
                               let uu____10362 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____10363 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____10362 uu____10363
                                in
                             let uu____10364 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____10364))
                  in
               let lecs1 =
                 let uu____10374 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____10433 = univs_and_uvars_of_lec this_lec  in
                        match uu____10433 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____10374 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10534 = lec_hd  in
                   match uu____10534 with
                   | (lbname,e,c) ->
                       let uu____10544 =
                         let uu____10549 =
                           let uu____10550 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10551 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10552 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10550 uu____10551 uu____10552
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10549)
                          in
                       let uu____10553 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10544 uu____10553
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10574 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10574 with
                         | FStar_Pervasives_Native.Some uu____10583 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10590 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10594 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10594 with
                              | (bs,kres) ->
                                  ((let uu____10632 =
                                      let uu____10633 =
                                        let uu____10636 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____10636
                                         in
                                      uu____10633.FStar_Syntax_Syntax.n  in
                                    match uu____10632 with
                                    | FStar_Syntax_Syntax.Tm_type uu____10637
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____10641 =
                                          let uu____10642 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____10642  in
                                        if uu____10641
                                        then fail1 kres
                                        else ()
                                    | uu____10644 -> fail1 kres);
                                   (let a =
                                      let uu____10646 =
                                        let uu____10649 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_19  ->
                                             FStar_Pervasives_Native.Some
                                               _0_19) uu____10649
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____10646
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____10657 ->
                                          let uu____10664 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____10664
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
                      (fun uu____10775  ->
                         match uu____10775 with
                         | (lbname,e,c) ->
                             let uu____10829 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____10904 ->
                                   let uu____10919 = (e, c)  in
                                   (match uu____10919 with
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
                                                (fun uu____10970  ->
                                                   match uu____10970 with
                                                   | (x,uu____10978) ->
                                                       let uu____10983 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____10983)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____11001 =
                                                let uu____11002 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____11002
                                                 in
                                              if uu____11001
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
                                          let uu____11008 =
                                            let uu____11009 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____11009.FStar_Syntax_Syntax.n
                                             in
                                          match uu____11008 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____11030 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____11030 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____11043 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____11047 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____11047, gen_tvars))
                                in
                             (match uu____10829 with
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
        (let uu____11201 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____11201
         then
           let uu____11202 =
             let uu____11203 =
               FStar_List.map
                 (fun uu____11216  ->
                    match uu____11216 with
                    | (lb,uu____11224,uu____11225) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____11203 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____11202
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____11246  ->
                match uu____11246 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____11275 = gen env is_rec lecs  in
           match uu____11275 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____11374  ->
                       match uu____11374 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____11436 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____11436
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11482  ->
                           match uu____11482 with
                           | (l,us,e,c,gvs) ->
                               let uu____11516 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11517 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11518 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11519 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11520 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11516 uu____11517 uu____11518
                                 uu____11519 uu____11520))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11561  ->
                match uu____11561 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11605 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11605, t, c, gvs)) univnames_lecs
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
              (let uu____11662 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11662 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11668 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____11668)
             in
          let is_var e1 =
            let uu____11677 =
              let uu____11678 = FStar_Syntax_Subst.compress e1  in
              uu____11678.FStar_Syntax_Syntax.n  in
            match uu____11677 with
            | FStar_Syntax_Syntax.Tm_name uu____11681 -> true
            | uu____11682 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___119_11702 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___119_11702.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___119_11702.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____11703 -> e2  in
          let env2 =
            let uu___120_11705 = env1  in
            let uu____11706 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___120_11705.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___120_11705.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___120_11705.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___120_11705.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___120_11705.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___120_11705.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___120_11705.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___120_11705.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___120_11705.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___120_11705.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___120_11705.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___120_11705.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___120_11705.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___120_11705.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___120_11705.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___120_11705.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____11706;
              FStar_TypeChecker_Env.is_iface =
                (uu___120_11705.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___120_11705.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___120_11705.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___120_11705.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___120_11705.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___120_11705.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___120_11705.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___120_11705.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___120_11705.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___120_11705.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___120_11705.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___120_11705.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___120_11705.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___120_11705.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___120_11705.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___120_11705.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___120_11705.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___120_11705.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___120_11705.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___120_11705.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___120_11705.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____11707 = check1 env2 t1 t2  in
          match uu____11707 with
          | FStar_Pervasives_Native.None  ->
              let uu____11714 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____11719 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____11714 uu____11719
          | FStar_Pervasives_Native.Some g ->
              ((let uu____11726 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____11726
                then
                  let uu____11727 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____11727
                else ());
               (let uu____11729 = decorate e t2  in (uu____11729, g)))
  
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
        let uu____11761 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____11761
        then
          let uu____11766 = discharge g1  in
          let uu____11767 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____11766, uu____11767)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____11774 =
               let uu____11775 =
                 let uu____11776 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____11776 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____11775
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____11774
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____11778 = destruct_comp c1  in
           match uu____11778 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____11795 = FStar_TypeChecker_Env.get_range env  in
                 let uu____11796 =
                   let uu____11801 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____11802 =
                     let uu____11803 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____11810 =
                       let uu____11819 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____11819]  in
                     uu____11803 :: uu____11810  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____11801 uu____11802  in
                 uu____11796 FStar_Pervasives_Native.None uu____11795  in
               ((let uu____11847 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____11847
                 then
                   let uu____11848 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____11848
                 else ());
                (let g2 =
                   let uu____11851 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____11851  in
                 let uu____11852 = discharge g2  in
                 let uu____11853 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____11852, uu____11853))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___88_11885 =
        match uu___88_11885 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____11893)::[] -> f fst1
        | uu____11910 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____11921 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____11921
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_or_e e =
        let uu____11932 =
          let uu____11933 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____11933  in
        FStar_All.pipe_right uu____11932
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_or_t t =
        let uu____11952 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____11952
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
         in
      let short_op_ite uu___89_11966 =
        match uu___89_11966 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11974)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11993)::[] ->
            let uu____12022 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____12022
              (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
        | uu____12023 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____12034 =
          let uu____12042 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____12042)  in
        let uu____12050 =
          let uu____12060 =
            let uu____12068 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____12068)  in
          let uu____12076 =
            let uu____12086 =
              let uu____12094 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____12094)  in
            let uu____12102 =
              let uu____12112 =
                let uu____12120 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____12120)  in
              let uu____12128 =
                let uu____12138 =
                  let uu____12146 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____12146)  in
                [uu____12138; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____12112 :: uu____12128  in
            uu____12086 :: uu____12102  in
          uu____12060 :: uu____12076  in
        uu____12034 :: uu____12050  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____12208 =
            FStar_Util.find_map table
              (fun uu____12223  ->
                 match uu____12223 with
                 | (x,mk1) ->
                     let uu____12240 = FStar_Ident.lid_equals x lid  in
                     if uu____12240
                     then
                       let uu____12243 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____12243
                     else FStar_Pervasives_Native.None)
             in
          (match uu____12208 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____12246 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____12252 =
      let uu____12253 = FStar_Syntax_Util.un_uinst l  in
      uu____12253.FStar_Syntax_Syntax.n  in
    match uu____12252 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____12257 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____12287)::uu____12288 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____12299 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____12306,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____12307))::uu____12308 -> bs
      | uu____12319 ->
          let uu____12320 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____12320 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____12324 =
                 let uu____12325 = FStar_Syntax_Subst.compress t  in
                 uu____12325.FStar_Syntax_Syntax.n  in
               (match uu____12324 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____12329) ->
                    let uu____12346 =
                      FStar_Util.prefix_until
                        (fun uu___90_12386  ->
                           match uu___90_12386 with
                           | (uu____12393,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____12394)) ->
                               false
                           | uu____12397 -> true) bs'
                       in
                    (match uu____12346 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____12432,uu____12433) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12505,uu____12506) ->
                         let uu____12579 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____12597  ->
                                   match uu____12597 with
                                   | (x,uu____12605) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____12579
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____12648  ->
                                     match uu____12648 with
                                     | (x,i) ->
                                         let uu____12667 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____12667, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12675 -> bs))
  
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
            let uu____12703 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12703
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
          let uu____12730 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____12730
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
        (let uu____12765 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____12765
         then
           ((let uu____12767 = FStar_Ident.text_of_lid lident  in
             d uu____12767);
            (let uu____12768 = FStar_Ident.text_of_lid lident  in
             let uu____12769 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____12768 uu____12769))
         else ());
        (let fv =
           let uu____12772 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____12772
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
         let uu____12782 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___121_12784 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___121_12784.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___121_12784.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___121_12784.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___121_12784.FStar_Syntax_Syntax.sigattrs)
           }), uu____12782))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___91_12800 =
        match uu___91_12800 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12801 -> false  in
      let reducibility uu___92_12807 =
        match uu___92_12807 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____12808 -> false  in
      let assumption uu___93_12814 =
        match uu___93_12814 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____12815 -> false  in
      let reification uu___94_12821 =
        match uu___94_12821 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____12822 -> true
        | uu____12823 -> false  in
      let inferred uu___95_12829 =
        match uu___95_12829 with
        | FStar_Syntax_Syntax.Discriminator uu____12830 -> true
        | FStar_Syntax_Syntax.Projector uu____12831 -> true
        | FStar_Syntax_Syntax.RecordType uu____12836 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____12845 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____12854 -> false  in
      let has_eq uu___96_12860 =
        match uu___96_12860 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____12861 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____12925 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12930 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____12934 =
        let uu____12935 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___97_12939  ->
                  match uu___97_12939 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____12940 -> false))
           in
        FStar_All.pipe_right uu____12935 Prims.op_Negation  in
      if uu____12934
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____12955 =
            let uu____12960 =
              let uu____12961 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____12961 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____12960)  in
          FStar_Errors.raise_error uu____12955 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____12973 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____12977 =
            let uu____12978 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____12978  in
          if uu____12977 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____12983),uu____12984) ->
              ((let uu____12994 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____12994
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____12998 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____12998
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____13004 ->
              let uu____13013 =
                let uu____13014 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____13014  in
              if uu____13013 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____13020 ->
              let uu____13027 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____13027 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____13031 ->
              let uu____13038 =
                let uu____13039 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____13039  in
              if uu____13038 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____13045 ->
              let uu____13046 =
                let uu____13047 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13047  in
              if uu____13046 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13053 ->
              let uu____13054 =
                let uu____13055 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____13055  in
              if uu____13054 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13061 ->
              let uu____13074 =
                let uu____13075 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____13075  in
              if uu____13074 then err'1 () else ()
          | uu____13081 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____13115 =
          let uu____13116 = FStar_Syntax_Subst.compress t1  in
          uu____13116.FStar_Syntax_Syntax.n  in
        match uu____13115 with
        | FStar_Syntax_Syntax.Tm_type uu____13119 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____13122 =
                 let uu____13127 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____13127
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____13122
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____13145 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____13145
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____13162 =
                                 let uu____13163 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____13163.FStar_Syntax_Syntax.n  in
                               match uu____13162 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____13167 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____13168 ->
            let uu____13181 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____13181 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____13207 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____13207
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____13209;
               FStar_Syntax_Syntax.index = uu____13210;
               FStar_Syntax_Syntax.sort = t2;_},uu____13212)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____13220,uu____13221) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____13263::[]) ->
            let uu____13294 =
              let uu____13295 = FStar_Syntax_Util.un_uinst head1  in
              uu____13295.FStar_Syntax_Syntax.n  in
            (match uu____13294 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____13299 -> false)
        | uu____13300 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Primops;
            FStar_TypeChecker_Normalize.Weak;
            FStar_TypeChecker_Normalize.HNF;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.Delta_constant;
            FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Iota] env t1
           in
        let res = aux_whnf env t2  in
        (let uu____13308 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____13308
         then
           let uu____13309 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____13309
         else ());
        res
       in aux g t
  