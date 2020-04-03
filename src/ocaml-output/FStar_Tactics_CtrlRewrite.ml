open Prims
type controller_ty =
  FStar_Syntax_Syntax.term ->
    (Prims.bool * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac
type rewriter_ty = unit FStar_Tactics_Monad.tac
let (do_rewrite :
  FStar_Tactics_Types.goal ->
    rewriter_ty ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun g0  ->
    fun rewriter  ->
      fun env  ->
        fun tm  ->
          let uu____36 =
            env.FStar_TypeChecker_Env.tc_term
              (let uu___5_44 = env  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___5_44.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___5_44.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___5_44.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___5_44.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___5_44.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___5_44.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___5_44.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___5_44.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___5_44.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___5_44.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___5_44.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___5_44.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___5_44.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___5_44.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___5_44.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___5_44.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___5_44.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.use_eq_strict =
                   (uu___5_44.FStar_TypeChecker_Env.use_eq_strict);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___5_44.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___5_44.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___5_44.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___5_44.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___5_44.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___5_44.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___5_44.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___5_44.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___5_44.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___5_44.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___5_44.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___5_44.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___5_44.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___5_44.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___5_44.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___5_44.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___5_44.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___5_44.FStar_TypeChecker_Env.try_solve_implicits_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___5_44.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.mpreprocess =
                   (uu___5_44.FStar_TypeChecker_Env.mpreprocess);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___5_44.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___5_44.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___5_44.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___5_44.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___5_44.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___5_44.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___5_44.FStar_TypeChecker_Env.strict_args_tab);
                 FStar_TypeChecker_Env.erasable_types_tab =
                   (uu___5_44.FStar_TypeChecker_Env.erasable_types_tab)
               }) tm
             in
          match uu____36 with
          | (uu____48,lcomp,g) ->
              let uu____51 =
                (let uu____55 =
                   FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lcomp  in
                 Prims.op_Negation uu____55) ||
                  (let uu____58 = FStar_TypeChecker_Env.is_trivial g  in
                   Prims.op_Negation uu____58)
                 in
              if uu____51
              then FStar_Tactics_Monad.ret tm
              else
                (let typ = lcomp.FStar_TypeChecker_Common.res_typ  in
                 let uu____66 =
                   FStar_Tactics_Monad.new_uvar "do_rewrite.rhs" env typ  in
                 FStar_Tactics_Monad.bind uu____66
                   (fun uu____81  ->
                      match uu____81 with
                      | (ut,uvar_ut) ->
                          FStar_Tactics_Monad.mlog
                            (fun uu____93  ->
                               let uu____94 =
                                 FStar_Syntax_Print.term_to_string tm  in
                               let uu____96 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "do_rewrite: making equality\n\t%s ==\n\t%s\n"
                                 uu____94 uu____96)
                            (fun uu____101  ->
                               let uu____102 =
                                 let uu____105 =
                                   let uu____106 =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env typ
                                      in
                                   FStar_Syntax_Util.mk_eq2 uu____106 typ tm
                                     ut
                                    in
                                 FStar_Tactics_Monad.add_irrelevant_goal g0
                                   "do_rewrite.eq" env uu____105
                                  in
                               FStar_Tactics_Monad.bind uu____102
                                 (fun uu____110  ->
                                    let uu____111 =
                                      FStar_Tactics_Basic.focus rewriter  in
                                    FStar_Tactics_Monad.bind uu____111
                                      (fun uu____116  ->
                                         let ut1 =
                                           FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                             env ut
                                            in
                                         FStar_Tactics_Monad.mlog
                                           (fun uu____121  ->
                                              let uu____122 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____124 =
                                                FStar_Syntax_Print.term_to_string
                                                  ut1
                                                 in
                                              FStar_Util.print2
                                                "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                uu____122 uu____124)
                                           (fun uu____128  ->
                                              FStar_Tactics_Monad.ret ut1))))))
  
type 'a ctac =
  'a -> ('a * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac
let seq_ctac : 'a . 'a ctac -> 'a ctac -> 'a ctac =
  fun c1  ->
    fun c2  ->
      fun x  ->
        let uu____176 = c1 x  in
        FStar_Tactics_Monad.bind uu____176
          (fun uu____194  ->
             match uu____194 with
             | (x',flag) ->
                 (match flag with
                  | FStar_Tactics_Types.Abort  ->
                      FStar_Tactics_Monad.ret (x', FStar_Tactics_Types.Abort)
                  | FStar_Tactics_Types.Skip  ->
                      FStar_Tactics_Monad.ret (x', FStar_Tactics_Types.Skip)
                  | FStar_Tactics_Types.Continue  -> c2 x'))
  
let (par_combine :
  (FStar_Tactics_Types.ctrl_flag * FStar_Tactics_Types.ctrl_flag) ->
    FStar_Tactics_Types.ctrl_flag)
  =
  fun uu___0_230  ->
    match uu___0_230 with
    | (FStar_Tactics_Types.Abort ,uu____235) -> FStar_Tactics_Types.Abort
    | (uu____236,FStar_Tactics_Types.Abort ) -> FStar_Tactics_Types.Abort
    | (FStar_Tactics_Types.Skip ,uu____237) -> FStar_Tactics_Types.Skip
    | (uu____238,FStar_Tactics_Types.Skip ) -> FStar_Tactics_Types.Skip
    | (FStar_Tactics_Types.Continue ,FStar_Tactics_Types.Continue ) ->
        FStar_Tactics_Types.Continue
  
let par_ctac : 'a 'b . 'a ctac -> 'b ctac -> ('a * 'b) ctac =
  fun cl  ->
    fun cr  ->
      fun uu____279  ->
        match uu____279 with
        | (x,y) ->
            let uu____296 = cl x  in
            FStar_Tactics_Monad.bind uu____296
              (fun uu____318  ->
                 match uu____318 with
                 | (x1,flag) ->
                     (match flag with
                      | FStar_Tactics_Types.Abort  ->
                          FStar_Tactics_Monad.ret
                            ((x1, y), FStar_Tactics_Types.Abort)
                      | fa ->
                          let uu____358 = cr y  in
                          FStar_Tactics_Monad.bind uu____358
                            (fun uu____380  ->
                               match uu____380 with
                               | (y1,flag1) ->
                                   (match flag1 with
                                    | FStar_Tactics_Types.Abort  ->
                                        FStar_Tactics_Monad.ret
                                          ((x1, y1),
                                            FStar_Tactics_Types.Abort)
                                    | fb ->
                                        FStar_Tactics_Monad.ret
                                          ((x1, y1), (par_combine (fa, fb)))))))
  
let rec map_ctac : 'a . 'a ctac -> 'a Prims.list ctac =
  fun c  ->
    fun xs  ->
      match xs with
      | [] -> FStar_Tactics_Monad.ret ([], FStar_Tactics_Types.Continue)
      | x::xs1 ->
          let uu____471 =
            let uu____484 =
              let uu____495 = map_ctac c  in par_ctac c uu____495  in
            uu____484 (x, xs1)  in
          FStar_Tactics_Monad.bind uu____471
            (fun uu____526  ->
               match uu____526 with
               | ((x1,xs2),flag) ->
                   FStar_Tactics_Monad.ret ((x1 :: xs2), flag))
  
let bind_ctac : 'a 'b . 'a ctac -> ('a -> 'b ctac) -> 'b ctac =
  fun t  -> fun f  -> fun b  -> failwith "" 
let ctac_id :
  'a . 'a -> ('a * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac =
  fun x  -> FStar_Tactics_Monad.ret (x, FStar_Tactics_Types.Continue) 
let (ctac_args :
  FStar_Syntax_Syntax.term ctac -> FStar_Syntax_Syntax.args ctac) =
  fun c  -> let uu____654 = par_ctac c ctac_id  in map_ctac uu____654 
let (maybe_rewrite :
  FStar_Tactics_Types.goal ->
    controller_ty ->
      rewriter_ty ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Tactics_Types.ctrl_flag)
              FStar_Tactics_Monad.tac)
  =
  fun g0  ->
    fun controller  ->
      fun rewriter  ->
        fun env  ->
          fun tm  ->
            let uu____715 = controller tm  in
            FStar_Tactics_Monad.bind uu____715
              (fun uu____736  ->
                 match uu____736 with
                 | (rw,ctrl_flag) ->
                     let uu____752 =
                       if rw
                       then do_rewrite g0 rewriter env tm
                       else FStar_Tactics_Monad.ret tm  in
                     FStar_Tactics_Monad.bind uu____752
                       (fun tm'  -> FStar_Tactics_Monad.ret (tm', ctrl_flag)))
  
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
  fun g0  ->
    fun d  ->
      fun controller  ->
        fun rewriter  ->
          fun env  ->
            fun tm  ->
              let recurse tm1 =
                ctrl_fold_env g0 d controller rewriter env tm1  in
              match d with
              | FStar_Tactics_Types.TopDown  ->
                  let uu____864 =
                    seq_ctac (maybe_rewrite g0 controller rewriter env)
                      (on_subterms g0 d controller rewriter env)
                     in
                  uu____864 tm
              | FStar_Tactics_Types.BottomUp  ->
                  let uu____869 =
                    seq_ctac (on_subterms g0 d controller rewriter env)
                      (maybe_rewrite g0 controller rewriter env)
                     in
                  uu____869 tm

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
  fun g0  ->
    fun d  ->
      fun controller  ->
        fun rewriter  ->
          fun env  ->
            fun tm  ->
              let recurse env1 tm1 =
                ctrl_fold_env g0 d controller rewriter env1 tm1  in
              let rr = recurse env  in
              let go uu____926 =
                let tm1 = FStar_Syntax_Subst.compress tm  in
                match tm1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                    let uu____966 =
                      let uu____977 =
                        let uu____986 = ctac_args rr  in
                        par_ctac rr uu____986  in
                      uu____977 (hd1, args)  in
                    FStar_Tactics_Monad.bind uu____966
                      (fun uu____1007  ->
                         match uu____1007 with
                         | ((hd2,args1),flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_app (hd2, args1)),
                                 flag))
                | FStar_Syntax_Syntax.Tm_abs (bs,t,k) ->
                    let uu____1072 = FStar_Syntax_Subst.open_term bs t  in
                    (match uu____1072 with
                     | (bs1,t1) ->
                         let uu____1085 =
                           let uu____1092 =
                             FStar_TypeChecker_Env.push_binders env bs1  in
                           recurse uu____1092 t1  in
                         FStar_Tactics_Monad.bind uu____1085
                           (fun uu____1105  ->
                              match uu____1105 with
                              | (t2,flag) ->
                                  let uu____1118 =
                                    let uu____1123 =
                                      let uu____1124 =
                                        let uu____1143 =
                                          FStar_Syntax_Subst.close_binders
                                            bs1
                                           in
                                        let uu____1152 =
                                          FStar_Syntax_Subst.close bs1 t2  in
                                        (uu____1143, uu____1152, k)  in
                                      FStar_Syntax_Syntax.Tm_abs uu____1124
                                       in
                                    (uu____1123, flag)  in
                                  FStar_Tactics_Monad.ret uu____1118))
                | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                    FStar_Tactics_Monad.ret
                      ((tm1.FStar_Syntax_Syntax.n),
                        FStar_Tactics_Types.Continue)
                | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                    let c_branch br =
                      let uu____1253 = FStar_Syntax_Subst.open_branch br  in
                      match uu____1253 with
                      | (pat,w,e) ->
                          let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                          let uu____1282 =
                            let uu____1289 =
                              FStar_TypeChecker_Env.push_bvs env bvs  in
                            recurse uu____1289 e  in
                          FStar_Tactics_Monad.bind uu____1282
                            (fun uu____1302  ->
                               match uu____1302 with
                               | (e1,flag) ->
                                   let br1 =
                                     FStar_Syntax_Subst.close_branch
                                       (pat, w, e1)
                                      in
                                   FStar_Tactics_Monad.ret (br1, flag))
                       in
                    let uu____1328 =
                      let uu____1341 =
                        let uu____1352 = map_ctac c_branch  in
                        par_ctac rr uu____1352  in
                      uu____1341 (hd1, brs)  in
                    FStar_Tactics_Monad.bind uu____1328
                      (fun uu____1381  ->
                         match uu____1381 with
                         | ((hd2,brs1),flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_match (hd2, brs1)),
                                 flag))
                | FStar_Syntax_Syntax.Tm_let
                    ((false
                      ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                         FStar_Syntax_Syntax.lbunivs = uu____1434;
                         FStar_Syntax_Syntax.lbtyp = uu____1435;
                         FStar_Syntax_Syntax.lbeff = uu____1436;
                         FStar_Syntax_Syntax.lbdef = def;
                         FStar_Syntax_Syntax.lbattrs = uu____1438;
                         FStar_Syntax_Syntax.lbpos = uu____1439;_}::[]),e)
                    ->
                    let lb =
                      let uu____1467 =
                        let uu____1468 = FStar_Syntax_Subst.compress tm1  in
                        uu____1468.FStar_Syntax_Syntax.n  in
                      match uu____1467 with
                      | FStar_Syntax_Syntax.Tm_let
                          ((false ,lb::[]),uu____1472) -> lb
                      | uu____1488 -> failwith "impossible"  in
                    let uu____1490 = FStar_Syntax_Subst.open_term_bv bv e  in
                    (match uu____1490 with
                     | (bv1,e1) ->
                         let uu____1503 =
                           let uu____1514 =
                             let uu____1523 =
                               let uu____1528 =
                                 FStar_TypeChecker_Env.push_bv env bv1  in
                               recurse uu____1528  in
                             par_ctac rr uu____1523  in
                           uu____1514 ((lb.FStar_Syntax_Syntax.lbdef), e1)
                            in
                         FStar_Tactics_Monad.bind uu____1503
                           (fun uu____1547  ->
                              match uu____1547 with
                              | ((lbdef,e2),flag) ->
                                  let lb1 =
                                    let uu___196_1570 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___196_1570.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___196_1570.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp =
                                        (uu___196_1570.FStar_Syntax_Syntax.lbtyp);
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___196_1570.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = lbdef;
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___196_1570.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___196_1570.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let e3 =
                                    let uu____1572 =
                                      let uu____1573 =
                                        FStar_Syntax_Syntax.mk_binder bv1  in
                                      [uu____1573]  in
                                    FStar_Syntax_Subst.close uu____1572 e2
                                     in
                                  FStar_Tactics_Monad.ret
                                    ((FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3)), flag)))
                | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                    let c_lb lb =
                      let uu____1646 = rr lb.FStar_Syntax_Syntax.lbdef  in
                      FStar_Tactics_Monad.bind uu____1646
                        (fun uu____1664  ->
                           match uu____1664 with
                           | (def,flag) ->
                               FStar_Tactics_Monad.ret
                                 ((let uu___211_1682 = lb  in
                                   {
                                     FStar_Syntax_Syntax.lbname =
                                       (uu___211_1682.FStar_Syntax_Syntax.lbname);
                                     FStar_Syntax_Syntax.lbunivs =
                                       (uu___211_1682.FStar_Syntax_Syntax.lbunivs);
                                     FStar_Syntax_Syntax.lbtyp =
                                       (uu___211_1682.FStar_Syntax_Syntax.lbtyp);
                                     FStar_Syntax_Syntax.lbeff =
                                       (uu___211_1682.FStar_Syntax_Syntax.lbeff);
                                     FStar_Syntax_Syntax.lbdef = def;
                                     FStar_Syntax_Syntax.lbattrs =
                                       (uu___211_1682.FStar_Syntax_Syntax.lbattrs);
                                     FStar_Syntax_Syntax.lbpos =
                                       (uu___211_1682.FStar_Syntax_Syntax.lbpos)
                                   }), flag))
                       in
                    let uu____1683 = FStar_Syntax_Subst.open_let_rec lbs e
                       in
                    (match uu____1683 with
                     | (lbs1,e1) ->
                         let uu____1702 =
                           let uu____1715 =
                             let uu____1726 = map_ctac c_lb  in
                             par_ctac uu____1726 rr  in
                           uu____1715 (lbs1, e1)  in
                         FStar_Tactics_Monad.bind uu____1702
                           (fun uu____1758  ->
                              match uu____1758 with
                              | ((lbs2,e2),flag) ->
                                  let uu____1788 =
                                    FStar_Syntax_Subst.close_let_rec lbs2 e2
                                     in
                                  (match uu____1788 with
                                   | (lbs3,e3) ->
                                       FStar_Tactics_Monad.ret
                                         ((FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)), flag))))
                | FStar_Syntax_Syntax.Tm_ascribed (t,asc,eff) ->
                    let uu____1867 = rr t  in
                    FStar_Tactics_Monad.bind uu____1867
                      (fun uu____1885  ->
                         match uu____1885 with
                         | (t1,flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_ascribed
                                   (t1, asc, eff)), flag))
                | FStar_Syntax_Syntax.Tm_meta (t,m) ->
                    let uu____1928 = rr t  in
                    FStar_Tactics_Monad.bind uu____1928
                      (fun uu____1946  ->
                         match uu____1946 with
                         | (t1,flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_meta (t1, m)), flag))
                | uu____1965 ->
                    FStar_Tactics_Monad.ret
                      ((tm1.FStar_Syntax_Syntax.n),
                        FStar_Tactics_Types.Continue)
                 in
              let uu____1970 = go ()  in
              FStar_Tactics_Monad.bind uu____1970
                (fun uu____1990  ->
                   match uu____1990 with
                   | (tmn',flag) ->
                       FStar_Tactics_Monad.ret
                         ((let uu___243_2014 = tm  in
                           {
                             FStar_Syntax_Syntax.n = tmn';
                             FStar_Syntax_Syntax.pos =
                               (uu___243_2014.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___243_2014.FStar_Syntax_Syntax.vars)
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
  fun g0  ->
    fun dir  ->
      fun controller  ->
        fun rewriter  ->
          fun env  ->
            fun tm  ->
              let uu____2052 =
                ctrl_fold_env g0 dir controller rewriter env tm  in
              FStar_Tactics_Monad.bind uu____2052
                (fun uu____2066  ->
                   match uu____2066 with
                   | (tm',uu____2074) -> FStar_Tactics_Monad.ret tm')
  
let (ctrl_rewrite :
  FStar_Tactics_Types.direction ->
    controller_ty -> rewriter_ty -> unit FStar_Tactics_Monad.tac)
  =
  fun dir  ->
    fun controller  ->
      fun rewriter  ->
        let uu____2097 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps  ->
               let uu____2105 =
                 match ps.FStar_Tactics_Types.goals with
                 | g::gs -> (g, gs)
                 | [] -> failwith "no goals"  in
               match uu____2105 with
               | (g,gs) ->
                   FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss_all
                     (fun uu____2143  ->
                        let gt1 = FStar_Tactics_Types.goal_type g  in
                        FStar_Tactics_Monad.log ps
                          (fun uu____2148  ->
                             let uu____2149 =
                               FStar_Syntax_Print.term_to_string gt1  in
                             FStar_Util.print1
                               "ctrl_rewrite starting with %s\n" uu____2149);
                        (let uu____2152 =
                           let uu____2155 = FStar_Tactics_Types.goal_env g
                              in
                           do_ctrl_rewrite g dir controller rewriter
                             uu____2155 gt1
                            in
                         FStar_Tactics_Monad.bind uu____2152
                           (fun gt'  ->
                              FStar_Tactics_Monad.log ps
                                (fun uu____2163  ->
                                   let uu____2164 =
                                     FStar_Syntax_Print.term_to_string gt'
                                      in
                                   FStar_Util.print1
                                     "ctrl_rewrite seems to have succeded with %s\n"
                                     uu____2164);
                              (let uu____2167 =
                                 FStar_Tactics_Monad.push_goals gs  in
                               FStar_Tactics_Monad.bind uu____2167
                                 (fun uu____2172  ->
                                    let uu____2173 =
                                      let uu____2176 =
                                        FStar_Tactics_Types.goal_with_type g
                                          gt'
                                         in
                                      [uu____2176]  in
                                    FStar_Tactics_Monad.add_goals uu____2173))))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "ctrl_rewrite")
          uu____2097
  