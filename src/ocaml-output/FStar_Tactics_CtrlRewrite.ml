open Prims
type controller_ty =
  FStar_Syntax_Syntax.term ->
    (Prims.bool * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac
type rewriter_ty = unit FStar_Tactics_Monad.tac
let (__do_rewrite :
  FStar_Tactics_Types.goal ->
    rewriter_ty ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun rewriter ->
      fun env ->
        fun tm ->
          let uu____35 =
            env.FStar_TypeChecker_Env.tc_term
              (let uu___6_43 = env in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___6_43.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___6_43.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___6_43.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___6_43.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___6_43.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___6_43.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___6_43.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___6_43.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___6_43.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___6_43.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___6_43.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___6_43.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___6_43.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___6_43.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___6_43.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___6_43.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___6_43.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.use_eq_strict =
                   (uu___6_43.FStar_TypeChecker_Env.use_eq_strict);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___6_43.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___6_43.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___6_43.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___6_43.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___6_43.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___6_43.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___6_43.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___6_43.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___6_43.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___6_43.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___6_43.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___6_43.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___6_43.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___6_43.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___6_43.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___6_43.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___6_43.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___6_43.FStar_TypeChecker_Env.try_solve_implicits_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___6_43.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.mpreprocess =
                   (uu___6_43.FStar_TypeChecker_Env.mpreprocess);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___6_43.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___6_43.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___6_43.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___6_43.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___6_43.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___6_43.FStar_TypeChecker_Env.strict_args_tab);
                 FStar_TypeChecker_Env.erasable_types_tab =
                   (uu___6_43.FStar_TypeChecker_Env.erasable_types_tab);
                 FStar_TypeChecker_Env.enable_defer_to_tac =
                   (uu___6_43.FStar_TypeChecker_Env.enable_defer_to_tac)
               }) tm in
          match uu____35 with
          | (uu____46, lcomp, g) ->
              let uu____49 =
                (let uu____52 =
                   FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lcomp in
                 Prims.op_Negation uu____52) ||
                  (let uu____54 = FStar_TypeChecker_Env.is_trivial g in
                   Prims.op_Negation uu____54) in
              if uu____49
              then FStar_Tactics_Monad.ret tm
              else
                (let typ = lcomp.FStar_TypeChecker_Common.res_typ in
                 let uu____59 =
                   FStar_Tactics_Monad.new_uvar "do_rewrite.rhs" env typ in
                 FStar_Tactics_Monad.bind uu____59
                   (fun uu____73 ->
                      match uu____73 with
                      | (ut, uvar_ut) ->
                          FStar_Tactics_Monad.mlog
                            (fun uu____85 ->
                               let uu____86 =
                                 FStar_Syntax_Print.term_to_string tm in
                               let uu____87 =
                                 FStar_Syntax_Print.term_to_string ut in
                               FStar_Util.print2
                                 "do_rewrite: making equality\n\t%s ==\n\t%s\n"
                                 uu____86 uu____87)
                            (fun uu____90 ->
                               let uu____91 =
                                 let uu____94 =
                                   let uu____95 =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env typ in
                                   FStar_Syntax_Util.mk_eq2 uu____95 typ tm
                                     ut in
                                 FStar_Tactics_Monad.add_irrelevant_goal g0
                                   "do_rewrite.eq" env uu____94 in
                               FStar_Tactics_Monad.bind uu____91
                                 (fun uu____98 ->
                                    let uu____99 =
                                      FStar_Tactics_Basic.focus rewriter in
                                    FStar_Tactics_Monad.bind uu____99
                                      (fun uu____104 ->
                                         let ut1 =
                                           FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                             env ut in
                                         FStar_Tactics_Monad.mlog
                                           (fun uu____109 ->
                                              let uu____110 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              let uu____111 =
                                                FStar_Syntax_Print.term_to_string
                                                  ut1 in
                                              FStar_Util.print2
                                                "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                uu____110 uu____111)
                                           (fun uu____113 ->
                                              FStar_Tactics_Monad.ret ut1))))))
let (do_rewrite :
  FStar_Tactics_Types.goal ->
    rewriter_ty ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun rewriter ->
      fun env ->
        fun tm ->
          let uu____138 =
            let uu____145 = __do_rewrite g0 rewriter env tm in
            FStar_Tactics_Basic.catch uu____145 in
          FStar_Tactics_Monad.bind uu____138
            (fun uu___0_153 ->
               match uu___0_153 with
               | FStar_Util.Inl (FStar_Tactics_Types.TacticFailure "SKIP") ->
                   FStar_Tactics_Monad.ret tm
               | FStar_Util.Inl e -> FStar_Tactics_Monad.traise e
               | FStar_Util.Inr tm' -> FStar_Tactics_Monad.ret tm')
type 'a ctac =
  'a -> ('a * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac
let seq_ctac : 'a . 'a ctac -> 'a ctac -> 'a ctac =
  fun c1 ->
    fun c2 ->
      fun x ->
        let uu____208 = c1 x in
        FStar_Tactics_Monad.bind uu____208
          (fun uu____226 ->
             match uu____226 with
             | (x', flag) ->
                 (match flag with
                  | FStar_Tactics_Types.Abort ->
                      FStar_Tactics_Monad.ret (x', FStar_Tactics_Types.Abort)
                  | FStar_Tactics_Types.Skip ->
                      FStar_Tactics_Monad.ret (x', FStar_Tactics_Types.Skip)
                  | FStar_Tactics_Types.Continue -> c2 x'))
let (par_combine :
  (FStar_Tactics_Types.ctrl_flag * FStar_Tactics_Types.ctrl_flag) ->
    FStar_Tactics_Types.ctrl_flag)
  =
  fun uu___1_261 ->
    match uu___1_261 with
    | (FStar_Tactics_Types.Abort, uu____266) -> FStar_Tactics_Types.Abort
    | (uu____267, FStar_Tactics_Types.Abort) -> FStar_Tactics_Types.Abort
    | (FStar_Tactics_Types.Skip, uu____268) -> FStar_Tactics_Types.Skip
    | (uu____269, FStar_Tactics_Types.Skip) -> FStar_Tactics_Types.Skip
    | (FStar_Tactics_Types.Continue, FStar_Tactics_Types.Continue) ->
        FStar_Tactics_Types.Continue
let par_ctac : 'a 'b . 'a ctac -> 'b ctac -> ('a * 'b) ctac =
  fun cl ->
    fun cr ->
      fun uu____309 ->
        match uu____309 with
        | (x, y) ->
            let uu____326 = cl x in
            FStar_Tactics_Monad.bind uu____326
              (fun uu____348 ->
                 match uu____348 with
                 | (x1, flag) ->
                     (match flag with
                      | FStar_Tactics_Types.Abort ->
                          FStar_Tactics_Monad.ret
                            ((x1, y), FStar_Tactics_Types.Abort)
                      | fa ->
                          let uu____388 = cr y in
                          FStar_Tactics_Monad.bind uu____388
                            (fun uu____410 ->
                               match uu____410 with
                               | (y1, flag1) ->
                                   (match flag1 with
                                    | FStar_Tactics_Types.Abort ->
                                        FStar_Tactics_Monad.ret
                                          ((x1, y1),
                                            FStar_Tactics_Types.Abort)
                                    | fb ->
                                        FStar_Tactics_Monad.ret
                                          ((x1, y1), (par_combine (fa, fb)))))))
let rec map_ctac : 'a . 'a ctac -> 'a Prims.list ctac =
  fun c ->
    fun xs ->
      match xs with
      | [] -> FStar_Tactics_Monad.ret ([], FStar_Tactics_Types.Continue)
      | x::xs1 ->
          let uu____500 =
            let uu____513 =
              let uu____524 = map_ctac c in par_ctac c uu____524 in
            uu____513 (x, xs1) in
          FStar_Tactics_Monad.bind uu____500
            (fun uu____555 ->
               match uu____555 with
               | ((x1, xs2), flag) ->
                   FStar_Tactics_Monad.ret ((x1 :: xs2), flag))
let bind_ctac : 'a 'b . 'a ctac -> ('a -> 'b ctac) -> 'b ctac =
  fun t -> fun f -> fun b1 -> failwith ""
let ctac_id :
  'a . 'a -> ('a * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac =
  fun x -> FStar_Tactics_Monad.ret (x, FStar_Tactics_Types.Continue)
let (ctac_args :
  FStar_Syntax_Syntax.term ctac -> FStar_Syntax_Syntax.args ctac) =
  fun c -> let uu____679 = par_ctac c ctac_id in map_ctac uu____679
let (maybe_rewrite :
  FStar_Tactics_Types.goal ->
    controller_ty ->
      rewriter_ty ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Tactics_Types.ctrl_flag)
              FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun controller ->
      fun rewriter ->
        fun env ->
          fun tm ->
            let uu____739 = controller tm in
            FStar_Tactics_Monad.bind uu____739
              (fun uu____758 ->
                 match uu____758 with
                 | (rw, ctrl_flag) ->
                     let uu____771 =
                       if rw
                       then do_rewrite g0 rewriter env tm
                       else FStar_Tactics_Monad.ret tm in
                     FStar_Tactics_Monad.bind uu____771
                       (fun tm' -> FStar_Tactics_Monad.ret (tm', ctrl_flag)))
let rec (ctrl_fold_env :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.direction ->
      controller_ty ->
        rewriter_ty ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term ->
              (FStar_Syntax_Syntax.term * FStar_Tactics_Types.ctrl_flag)
                FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun d ->
      fun controller ->
        fun rewriter ->
          fun env ->
            fun tm ->
              let recurse tm1 =
                ctrl_fold_env g0 d controller rewriter env tm1 in
              match d with
              | FStar_Tactics_Types.TopDown ->
                  let uu____880 =
                    seq_ctac (maybe_rewrite g0 controller rewriter env)
                      (on_subterms g0 d controller rewriter env) in
                  uu____880 tm
              | FStar_Tactics_Types.BottomUp ->
                  let uu____885 =
                    seq_ctac (on_subterms g0 d controller rewriter env)
                      (maybe_rewrite g0 controller rewriter env) in
                  uu____885 tm
and (on_subterms :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.direction ->
      controller_ty ->
        rewriter_ty ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term ->
              (FStar_Syntax_Syntax.term * FStar_Tactics_Types.ctrl_flag)
                FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun d ->
      fun controller ->
        fun rewriter ->
          fun env ->
            fun tm ->
              let recurse env1 tm1 =
                ctrl_fold_env g0 d controller rewriter env1 tm1 in
              let rr = recurse env in
              let go uu____942 =
                let tm1 = FStar_Syntax_Subst.compress tm in
                match tm1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_app (hd, args) ->
                    let uu____982 =
                      let uu____993 =
                        let uu____1002 = ctac_args rr in
                        par_ctac rr uu____1002 in
                      uu____993 (hd, args) in
                    FStar_Tactics_Monad.bind uu____982
                      (fun uu____1023 ->
                         match uu____1023 with
                         | ((hd1, args1), flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_app (hd1, args1)),
                                 flag))
                | FStar_Syntax_Syntax.Tm_abs (bs, t, k) ->
                    let uu____1088 = FStar_Syntax_Subst.open_term bs t in
                    (match uu____1088 with
                     | (bs1, t1) ->
                         let uu____1101 =
                           let uu____1108 =
                             FStar_TypeChecker_Env.push_binders env bs1 in
                           recurse uu____1108 t1 in
                         FStar_Tactics_Monad.bind uu____1101
                           (fun uu____1121 ->
                              match uu____1121 with
                              | (t2, flag) ->
                                  let uu____1134 =
                                    let uu____1139 =
                                      let uu____1140 =
                                        let uu____1159 =
                                          FStar_Syntax_Subst.close_binders
                                            bs1 in
                                        let uu____1168 =
                                          FStar_Syntax_Subst.close bs1 t2 in
                                        (uu____1159, uu____1168, k) in
                                      FStar_Syntax_Syntax.Tm_abs uu____1140 in
                                    (uu____1139, flag) in
                                  FStar_Tactics_Monad.ret uu____1134))
                | FStar_Syntax_Syntax.Tm_arrow (bs, k) ->
                    FStar_Tactics_Monad.ret
                      ((tm1.FStar_Syntax_Syntax.n),
                        FStar_Tactics_Types.Continue)
                | FStar_Syntax_Syntax.Tm_match (hd, brs) ->
                    let c_branch br =
                      let uu____1269 = FStar_Syntax_Subst.open_branch br in
                      match uu____1269 with
                      | (pat, w, e) ->
                          let bvs = FStar_Syntax_Syntax.pat_bvs pat in
                          let uu____1298 =
                            let uu____1305 =
                              FStar_TypeChecker_Env.push_bvs env bvs in
                            recurse uu____1305 e in
                          FStar_Tactics_Monad.bind uu____1298
                            (fun uu____1318 ->
                               match uu____1318 with
                               | (e1, flag) ->
                                   let br1 =
                                     FStar_Syntax_Subst.close_branch
                                       (pat, w, e1) in
                                   FStar_Tactics_Monad.ret (br1, flag)) in
                    let uu____1344 =
                      let uu____1357 =
                        let uu____1368 = map_ctac c_branch in
                        par_ctac rr uu____1368 in
                      uu____1357 (hd, brs) in
                    FStar_Tactics_Monad.bind uu____1344
                      (fun uu____1397 ->
                         match uu____1397 with
                         | ((hd1, brs1), flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_match (hd1, brs1)),
                                 flag))
                | FStar_Syntax_Syntax.Tm_let
                    ((false,
                      { FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                        FStar_Syntax_Syntax.lbunivs = uu____1450;
                        FStar_Syntax_Syntax.lbtyp = uu____1451;
                        FStar_Syntax_Syntax.lbeff = uu____1452;
                        FStar_Syntax_Syntax.lbdef = def;
                        FStar_Syntax_Syntax.lbattrs = uu____1454;
                        FStar_Syntax_Syntax.lbpos = uu____1455;_}::[]),
                     e)
                    ->
                    let lb =
                      let uu____1480 =
                        let uu____1481 = FStar_Syntax_Subst.compress tm1 in
                        uu____1481.FStar_Syntax_Syntax.n in
                      match uu____1480 with
                      | FStar_Syntax_Syntax.Tm_let
                          ((false, lb::[]), uu____1485) -> lb
                      | uu____1498 -> failwith "impossible" in
                    let uu____1499 = FStar_Syntax_Subst.open_term_bv bv e in
                    (match uu____1499 with
                     | (bv1, e1) ->
                         let uu____1512 =
                           let uu____1523 =
                             let uu____1532 =
                               let uu____1537 =
                                 FStar_TypeChecker_Env.push_bv env bv1 in
                               recurse uu____1537 in
                             par_ctac rr uu____1532 in
                           uu____1523 ((lb.FStar_Syntax_Syntax.lbdef), e1) in
                         FStar_Tactics_Monad.bind uu____1512
                           (fun uu____1556 ->
                              match uu____1556 with
                              | ((lbdef, e2), flag) ->
                                  let lb1 =
                                    let uu___209_1579 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___209_1579.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___209_1579.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp =
                                        (uu___209_1579.FStar_Syntax_Syntax.lbtyp);
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___209_1579.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = lbdef;
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___209_1579.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___209_1579.FStar_Syntax_Syntax.lbpos)
                                    } in
                                  let e3 =
                                    let uu____1581 =
                                      let uu____1582 =
                                        FStar_Syntax_Syntax.mk_binder bv1 in
                                      [uu____1582] in
                                    FStar_Syntax_Subst.close uu____1581 e2 in
                                  FStar_Tactics_Monad.ret
                                    ((FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3)), flag)))
                | FStar_Syntax_Syntax.Tm_let ((true, lbs), e) ->
                    let c_lb lb =
                      let uu____1649 = rr lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Tactics_Monad.bind uu____1649
                        (fun uu____1667 ->
                           match uu____1667 with
                           | (def, flag) ->
                               FStar_Tactics_Monad.ret
                                 ((let uu___224_1685 = lb in
                                   {
                                     FStar_Syntax_Syntax.lbname =
                                       (uu___224_1685.FStar_Syntax_Syntax.lbname);
                                     FStar_Syntax_Syntax.lbunivs =
                                       (uu___224_1685.FStar_Syntax_Syntax.lbunivs);
                                     FStar_Syntax_Syntax.lbtyp =
                                       (uu___224_1685.FStar_Syntax_Syntax.lbtyp);
                                     FStar_Syntax_Syntax.lbeff =
                                       (uu___224_1685.FStar_Syntax_Syntax.lbeff);
                                     FStar_Syntax_Syntax.lbdef = def;
                                     FStar_Syntax_Syntax.lbattrs =
                                       (uu___224_1685.FStar_Syntax_Syntax.lbattrs);
                                     FStar_Syntax_Syntax.lbpos =
                                       (uu___224_1685.FStar_Syntax_Syntax.lbpos)
                                   }), flag)) in
                    let uu____1686 = FStar_Syntax_Subst.open_let_rec lbs e in
                    (match uu____1686 with
                     | (lbs1, e1) ->
                         let uu____1705 =
                           let uu____1718 =
                             let uu____1729 = map_ctac c_lb in
                             par_ctac uu____1729 rr in
                           uu____1718 (lbs1, e1) in
                         FStar_Tactics_Monad.bind uu____1705
                           (fun uu____1761 ->
                              match uu____1761 with
                              | ((lbs2, e2), flag) ->
                                  let uu____1791 =
                                    FStar_Syntax_Subst.close_let_rec lbs2 e2 in
                                  (match uu____1791 with
                                   | (lbs3, e3) ->
                                       FStar_Tactics_Monad.ret
                                         ((FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)), flag))))
                | FStar_Syntax_Syntax.Tm_ascribed (t, asc, eff) ->
                    let uu____1867 = rr t in
                    FStar_Tactics_Monad.bind uu____1867
                      (fun uu____1885 ->
                         match uu____1885 with
                         | (t1, flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_ascribed
                                   (t1, asc, eff)), flag))
                | FStar_Syntax_Syntax.Tm_meta (t, m) ->
                    let uu____1928 = rr t in
                    FStar_Tactics_Monad.bind uu____1928
                      (fun uu____1946 ->
                         match uu____1946 with
                         | (t1, flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_meta (t1, m)), flag))
                | uu____1965 ->
                    FStar_Tactics_Monad.ret
                      ((tm1.FStar_Syntax_Syntax.n),
                        FStar_Tactics_Types.Continue) in
              let uu____1970 = go () in
              FStar_Tactics_Monad.bind uu____1970
                (fun uu____1990 ->
                   match uu____1990 with
                   | (tmn', flag) ->
                       FStar_Tactics_Monad.ret
                         ((let uu___256_2014 = tm in
                           {
                             FStar_Syntax_Syntax.n = tmn';
                             FStar_Syntax_Syntax.pos =
                               (uu___256_2014.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___256_2014.FStar_Syntax_Syntax.vars)
                           }), flag))
let (do_ctrl_rewrite :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.direction ->
      controller_ty ->
        rewriter_ty ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun g0 ->
    fun dir ->
      fun controller ->
        fun rewriter ->
          fun env ->
            fun tm ->
              let uu____2051 =
                ctrl_fold_env g0 dir controller rewriter env tm in
              FStar_Tactics_Monad.bind uu____2051
                (fun uu____2065 ->
                   match uu____2065 with
                   | (tm', uu____2073) -> FStar_Tactics_Monad.ret tm')
let (ctrl_rewrite :
  FStar_Tactics_Types.direction ->
    controller_ty -> rewriter_ty -> unit FStar_Tactics_Monad.tac)
  =
  fun dir ->
    fun controller ->
      fun rewriter ->
        let uu____2095 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____2103 =
                 match ps.FStar_Tactics_Types.goals with
                 | g::gs -> (g, gs)
                 | [] -> failwith "no goals" in
               match uu____2103 with
               | (g, gs) ->
                   FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss_all
                     (fun uu____2140 ->
                        let gt = FStar_Tactics_Types.goal_type g in
                        FStar_Tactics_Monad.log ps
                          (fun uu____2145 ->
                             let uu____2146 =
                               FStar_Syntax_Print.term_to_string gt in
                             FStar_Util.print1
                               "ctrl_rewrite starting with %s\n" uu____2146);
                        (let uu____2147 =
                           let uu____2150 = FStar_Tactics_Types.goal_env g in
                           do_ctrl_rewrite g dir controller rewriter
                             uu____2150 gt in
                         FStar_Tactics_Monad.bind uu____2147
                           (fun gt' ->
                              FStar_Tactics_Monad.log ps
                                (fun uu____2158 ->
                                   let uu____2159 =
                                     FStar_Syntax_Print.term_to_string gt' in
                                   FStar_Util.print1
                                     "ctrl_rewrite seems to have succeded with %s\n"
                                     uu____2159);
                              (let uu____2160 =
                                 FStar_Tactics_Monad.push_goals gs in
                               FStar_Tactics_Monad.bind uu____2160
                                 (fun uu____2165 ->
                                    let uu____2166 =
                                      let uu____2169 =
                                        FStar_Tactics_Types.goal_with_type g
                                          gt' in
                                      [uu____2169] in
                                    FStar_Tactics_Monad.add_goals uu____2166)))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "ctrl_rewrite")
          uu____2095