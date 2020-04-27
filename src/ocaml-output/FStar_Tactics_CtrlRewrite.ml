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
  fun g0  ->
    fun rewriter  ->
      fun env  ->
        fun tm  ->
          let uu____36 =
            env.FStar_TypeChecker_Env.tc_term
              (let uu___6_44 = env  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___6_44.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___6_44.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___6_44.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___6_44.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___6_44.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___6_44.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___6_44.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___6_44.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___6_44.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___6_44.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___6_44.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___6_44.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___6_44.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___6_44.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___6_44.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___6_44.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___6_44.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.use_eq_strict =
                   (uu___6_44.FStar_TypeChecker_Env.use_eq_strict);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___6_44.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___6_44.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___6_44.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___6_44.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___6_44.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___6_44.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___6_44.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___6_44.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___6_44.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___6_44.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___6_44.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___6_44.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___6_44.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___6_44.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___6_44.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___6_44.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___6_44.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (uu___6_44.FStar_TypeChecker_Env.try_solve_implicits_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___6_44.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.mpreprocess =
                   (uu___6_44.FStar_TypeChecker_Env.mpreprocess);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___6_44.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___6_44.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___6_44.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___6_44.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___6_44.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___6_44.FStar_TypeChecker_Env.strict_args_tab);
                 FStar_TypeChecker_Env.erasable_types_tab =
                   (uu___6_44.FStar_TypeChecker_Env.erasable_types_tab)
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
          let uu____154 =
            let uu____161 = __do_rewrite g0 rewriter env tm  in
            FStar_Tactics_Basic.catch uu____161  in
          FStar_Tactics_Monad.bind uu____154
            (fun uu___0_169  ->
               match uu___0_169 with
               | FStar_Util.Inl (FStar_Tactics_Types.TacticFailure "SKIP") ->
                   FStar_Tactics_Monad.ret tm
               | FStar_Util.Inl e -> FStar_Tactics_Monad.traise e
               | FStar_Util.Inr tm' -> FStar_Tactics_Monad.ret tm')
  
type 'a ctac =
  'a -> ('a * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac
let seq_ctac : 'a . 'a ctac -> 'a ctac -> 'a ctac =
  fun c1  ->
    fun c2  ->
      fun x  ->
        let uu____226 = c1 x  in
        FStar_Tactics_Monad.bind uu____226
          (fun uu____244  ->
             match uu____244 with
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
  fun uu___1_280  ->
    match uu___1_280 with
    | (FStar_Tactics_Types.Abort ,uu____285) -> FStar_Tactics_Types.Abort
    | (uu____286,FStar_Tactics_Types.Abort ) -> FStar_Tactics_Types.Abort
    | (FStar_Tactics_Types.Skip ,uu____287) -> FStar_Tactics_Types.Skip
    | (uu____288,FStar_Tactics_Types.Skip ) -> FStar_Tactics_Types.Skip
    | (FStar_Tactics_Types.Continue ,FStar_Tactics_Types.Continue ) ->
        FStar_Tactics_Types.Continue
  
let par_ctac : 'a 'b . 'a ctac -> 'b ctac -> ('a * 'b) ctac =
  fun cl  ->
    fun cr  ->
      fun uu____329  ->
        match uu____329 with
        | (x,y) ->
            let uu____346 = cl x  in
            FStar_Tactics_Monad.bind uu____346
              (fun uu____368  ->
                 match uu____368 with
                 | (x1,flag) ->
                     (match flag with
                      | FStar_Tactics_Types.Abort  ->
                          FStar_Tactics_Monad.ret
                            ((x1, y), FStar_Tactics_Types.Abort)
                      | fa ->
                          let uu____408 = cr y  in
                          FStar_Tactics_Monad.bind uu____408
                            (fun uu____430  ->
                               match uu____430 with
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
          let uu____521 =
            let uu____534 =
              let uu____545 = map_ctac c  in par_ctac c uu____545  in
            uu____534 (x, xs1)  in
          FStar_Tactics_Monad.bind uu____521
            (fun uu____576  ->
               match uu____576 with
               | ((x1,xs2),flag) ->
                   FStar_Tactics_Monad.ret ((x1 :: xs2), flag))
  
let bind_ctac : 'a 'b . 'a ctac -> ('a -> 'b ctac) -> 'b ctac =
  fun t  -> fun f  -> fun b1  -> failwith "" 
let ctac_id :
  'a . 'a -> ('a * FStar_Tactics_Types.ctrl_flag) FStar_Tactics_Monad.tac =
  fun x  -> FStar_Tactics_Monad.ret (x, FStar_Tactics_Types.Continue) 
let (ctac_args :
  FStar_Syntax_Syntax.term ctac -> FStar_Syntax_Syntax.args ctac) =
  fun c  -> let uu____704 = par_ctac c ctac_id  in map_ctac uu____704 
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
            let uu____765 = controller tm  in
            FStar_Tactics_Monad.bind uu____765
              (fun uu____786  ->
                 match uu____786 with
                 | (rw,ctrl_flag) ->
                     let uu____802 =
                       if rw
                       then do_rewrite g0 rewriter env tm
                       else FStar_Tactics_Monad.ret tm  in
                     FStar_Tactics_Monad.bind uu____802
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
                  let uu____914 =
                    seq_ctac (maybe_rewrite g0 controller rewriter env)
                      (on_subterms g0 d controller rewriter env)
                     in
                  uu____914 tm
              | FStar_Tactics_Types.BottomUp  ->
                  let uu____919 =
                    seq_ctac (on_subterms g0 d controller rewriter env)
                      (maybe_rewrite g0 controller rewriter env)
                     in
                  uu____919 tm

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
              let go uu____976 =
                let tm1 = FStar_Syntax_Subst.compress tm  in
                match tm1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_app (hd,args) ->
                    let uu____1016 =
                      let uu____1027 =
                        let uu____1036 = ctac_args rr  in
                        par_ctac rr uu____1036  in
                      uu____1027 (hd, args)  in
                    FStar_Tactics_Monad.bind uu____1016
                      (fun uu____1057  ->
                         match uu____1057 with
                         | ((hd1,args1),flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_app (hd1, args1)),
                                 flag))
                | FStar_Syntax_Syntax.Tm_abs (bs,t,k) ->
                    let uu____1122 = FStar_Syntax_Subst.open_term bs t  in
                    (match uu____1122 with
                     | (bs1,t1) ->
                         let uu____1135 =
                           let uu____1142 =
                             FStar_TypeChecker_Env.push_binders env bs1  in
                           recurse uu____1142 t1  in
                         FStar_Tactics_Monad.bind uu____1135
                           (fun uu____1155  ->
                              match uu____1155 with
                              | (t2,flag) ->
                                  let uu____1168 =
                                    let uu____1173 =
                                      let uu____1174 =
                                        let uu____1193 =
                                          FStar_Syntax_Subst.close_binders
                                            bs1
                                           in
                                        let uu____1202 =
                                          FStar_Syntax_Subst.close bs1 t2  in
                                        (uu____1193, uu____1202, k)  in
                                      FStar_Syntax_Syntax.Tm_abs uu____1174
                                       in
                                    (uu____1173, flag)  in
                                  FStar_Tactics_Monad.ret uu____1168))
                | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                    FStar_Tactics_Monad.ret
                      ((tm1.FStar_Syntax_Syntax.n),
                        FStar_Tactics_Types.Continue)
                | FStar_Syntax_Syntax.Tm_match (hd,brs) ->
                    let c_branch br =
                      let uu____1303 = FStar_Syntax_Subst.open_branch br  in
                      match uu____1303 with
                      | (pat,w,e) ->
                          let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                          let uu____1332 =
                            let uu____1339 =
                              FStar_TypeChecker_Env.push_bvs env bvs  in
                            recurse uu____1339 e  in
                          FStar_Tactics_Monad.bind uu____1332
                            (fun uu____1352  ->
                               match uu____1352 with
                               | (e1,flag) ->
                                   let br1 =
                                     FStar_Syntax_Subst.close_branch
                                       (pat, w, e1)
                                      in
                                   FStar_Tactics_Monad.ret (br1, flag))
                       in
                    let uu____1378 =
                      let uu____1391 =
                        let uu____1402 = map_ctac c_branch  in
                        par_ctac rr uu____1402  in
                      uu____1391 (hd, brs)  in
                    FStar_Tactics_Monad.bind uu____1378
                      (fun uu____1431  ->
                         match uu____1431 with
                         | ((hd1,brs1),flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_match (hd1, brs1)),
                                 flag))
                | FStar_Syntax_Syntax.Tm_let
                    ((false
                      ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                         FStar_Syntax_Syntax.lbunivs = uu____1484;
                         FStar_Syntax_Syntax.lbtyp = uu____1485;
                         FStar_Syntax_Syntax.lbeff = uu____1486;
                         FStar_Syntax_Syntax.lbdef = def;
                         FStar_Syntax_Syntax.lbattrs = uu____1488;
                         FStar_Syntax_Syntax.lbpos = uu____1489;_}::[]),e)
                    ->
                    let lb =
                      let uu____1517 =
                        let uu____1518 = FStar_Syntax_Subst.compress tm1  in
                        uu____1518.FStar_Syntax_Syntax.n  in
                      match uu____1517 with
                      | FStar_Syntax_Syntax.Tm_let
                          ((false ,lb::[]),uu____1522) -> lb
                      | uu____1538 -> failwith "impossible"  in
                    let uu____1540 = FStar_Syntax_Subst.open_term_bv bv e  in
                    (match uu____1540 with
                     | (bv1,e1) ->
                         let uu____1553 =
                           let uu____1564 =
                             let uu____1573 =
                               let uu____1578 =
                                 FStar_TypeChecker_Env.push_bv env bv1  in
                               recurse uu____1578  in
                             par_ctac rr uu____1573  in
                           uu____1564 ((lb.FStar_Syntax_Syntax.lbdef), e1)
                            in
                         FStar_Tactics_Monad.bind uu____1553
                           (fun uu____1597  ->
                              match uu____1597 with
                              | ((lbdef,e2),flag) ->
                                  let lb1 =
                                    let uu___209_1620 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___209_1620.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___209_1620.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp =
                                        (uu___209_1620.FStar_Syntax_Syntax.lbtyp);
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___209_1620.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = lbdef;
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___209_1620.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___209_1620.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let e3 =
                                    let uu____1622 =
                                      let uu____1623 =
                                        FStar_Syntax_Syntax.mk_binder bv1  in
                                      [uu____1623]  in
                                    FStar_Syntax_Subst.close uu____1622 e2
                                     in
                                  FStar_Tactics_Monad.ret
                                    ((FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3)), flag)))
                | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                    let c_lb lb =
                      let uu____1696 = rr lb.FStar_Syntax_Syntax.lbdef  in
                      FStar_Tactics_Monad.bind uu____1696
                        (fun uu____1714  ->
                           match uu____1714 with
                           | (def,flag) ->
                               FStar_Tactics_Monad.ret
                                 ((let uu___224_1732 = lb  in
                                   {
                                     FStar_Syntax_Syntax.lbname =
                                       (uu___224_1732.FStar_Syntax_Syntax.lbname);
                                     FStar_Syntax_Syntax.lbunivs =
                                       (uu___224_1732.FStar_Syntax_Syntax.lbunivs);
                                     FStar_Syntax_Syntax.lbtyp =
                                       (uu___224_1732.FStar_Syntax_Syntax.lbtyp);
                                     FStar_Syntax_Syntax.lbeff =
                                       (uu___224_1732.FStar_Syntax_Syntax.lbeff);
                                     FStar_Syntax_Syntax.lbdef = def;
                                     FStar_Syntax_Syntax.lbattrs =
                                       (uu___224_1732.FStar_Syntax_Syntax.lbattrs);
                                     FStar_Syntax_Syntax.lbpos =
                                       (uu___224_1732.FStar_Syntax_Syntax.lbpos)
                                   }), flag))
                       in
                    let uu____1733 = FStar_Syntax_Subst.open_let_rec lbs e
                       in
                    (match uu____1733 with
                     | (lbs1,e1) ->
                         let uu____1752 =
                           let uu____1765 =
                             let uu____1776 = map_ctac c_lb  in
                             par_ctac uu____1776 rr  in
                           uu____1765 (lbs1, e1)  in
                         FStar_Tactics_Monad.bind uu____1752
                           (fun uu____1808  ->
                              match uu____1808 with
                              | ((lbs2,e2),flag) ->
                                  let uu____1838 =
                                    FStar_Syntax_Subst.close_let_rec lbs2 e2
                                     in
                                  (match uu____1838 with
                                   | (lbs3,e3) ->
                                       FStar_Tactics_Monad.ret
                                         ((FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)), flag))))
                | FStar_Syntax_Syntax.Tm_ascribed (t,asc,eff) ->
                    let uu____1917 = rr t  in
                    FStar_Tactics_Monad.bind uu____1917
                      (fun uu____1935  ->
                         match uu____1935 with
                         | (t1,flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_ascribed
                                   (t1, asc, eff)), flag))
                | FStar_Syntax_Syntax.Tm_meta (t,m) ->
                    let uu____1978 = rr t  in
                    FStar_Tactics_Monad.bind uu____1978
                      (fun uu____1996  ->
                         match uu____1996 with
                         | (t1,flag) ->
                             FStar_Tactics_Monad.ret
                               ((FStar_Syntax_Syntax.Tm_meta (t1, m)), flag))
                | uu____2015 ->
                    FStar_Tactics_Monad.ret
                      ((tm1.FStar_Syntax_Syntax.n),
                        FStar_Tactics_Types.Continue)
                 in
              let uu____2020 = go ()  in
              FStar_Tactics_Monad.bind uu____2020
                (fun uu____2040  ->
                   match uu____2040 with
                   | (tmn',flag) ->
                       FStar_Tactics_Monad.ret
                         ((let uu___256_2064 = tm  in
                           {
                             FStar_Syntax_Syntax.n = tmn';
                             FStar_Syntax_Syntax.pos =
                               (uu___256_2064.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___256_2064.FStar_Syntax_Syntax.vars)
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
              let uu____2102 =
                ctrl_fold_env g0 dir controller rewriter env tm  in
              FStar_Tactics_Monad.bind uu____2102
                (fun uu____2116  ->
                   match uu____2116 with
                   | (tm',uu____2124) -> FStar_Tactics_Monad.ret tm')
  
let (ctrl_rewrite :
  FStar_Tactics_Types.direction ->
    controller_ty -> rewriter_ty -> unit FStar_Tactics_Monad.tac)
  =
  fun dir  ->
    fun controller  ->
      fun rewriter  ->
        let uu____2147 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps  ->
               let uu____2155 =
                 match ps.FStar_Tactics_Types.goals with
                 | g::gs -> (g, gs)
                 | [] -> failwith "no goals"  in
               match uu____2155 with
               | (g,gs) ->
                   FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss_all
                     (fun uu____2193  ->
                        let gt = FStar_Tactics_Types.goal_type g  in
                        FStar_Tactics_Monad.log ps
                          (fun uu____2198  ->
                             let uu____2199 =
                               FStar_Syntax_Print.term_to_string gt  in
                             FStar_Util.print1
                               "ctrl_rewrite starting with %s\n" uu____2199);
                        (let uu____2202 =
                           let uu____2205 = FStar_Tactics_Types.goal_env g
                              in
                           do_ctrl_rewrite g dir controller rewriter
                             uu____2205 gt
                            in
                         FStar_Tactics_Monad.bind uu____2202
                           (fun gt'  ->
                              FStar_Tactics_Monad.log ps
                                (fun uu____2213  ->
                                   let uu____2214 =
                                     FStar_Syntax_Print.term_to_string gt'
                                      in
                                   FStar_Util.print1
                                     "ctrl_rewrite seems to have succeded with %s\n"
                                     uu____2214);
                              (let uu____2217 =
                                 FStar_Tactics_Monad.push_goals gs  in
                               FStar_Tactics_Monad.bind uu____2217
                                 (fun uu____2222  ->
                                    let uu____2223 =
                                      let uu____2226 =
                                        FStar_Tactics_Types.goal_with_type g
                                          gt'
                                         in
                                      [uu____2226]  in
                                    FStar_Tactics_Monad.add_goals uu____2223))))))
           in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "ctrl_rewrite")
          uu____2147
  