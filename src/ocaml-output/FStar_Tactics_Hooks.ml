open Prims
let (run_tactic_on_typ :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term ->
            (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term))
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun typ  ->
            let rng =
              let uu____38 = FStar_Range.use_range rng_goal  in
              let uu____39 = FStar_Range.use_range rng_tac  in
              FStar_Range.range_of_rng uu____38 uu____39  in
            let uu____40 =
              FStar_Tactics_Basic.proofstate_of_goal_ty rng env typ  in
            match uu____40 with
            | (ps,w) ->
                let uu____53 =
                  FStar_Tactics_Interpreter.run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic ps
                   in
                (match uu____53 with | (gs,_res) -> (gs, w))
  
let (run_tactic_on_all_implicits :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_TypeChecker_Env.implicits ->
            FStar_Tactics_Types.goal Prims.list)
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun imps  ->
            let uu____104 =
              FStar_Tactics_Basic.proofstate_of_all_implicits rng_goal env
                imps
               in
            match uu____104 with
            | (ps,uu____112) ->
                let uu____113 =
                  FStar_Tactics_Interpreter.run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic ps
                   in
                (match uu____113 with | (goals,()) -> goals)
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____136 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____147 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Both  -> true | uu____158 -> false 
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____217 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____261 -> false
  
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____319 -> false
  
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'uuuuuu362 . 'uuuuuu362 -> 'uuuuuu362 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol1  ->
    fun e  ->
      fun t  ->
        let uu____392 = FStar_Syntax_Util.head_and_args t  in
        match uu____392 with
        | (hd,args) ->
            let uu____435 =
              let uu____450 =
                let uu____451 = FStar_Syntax_Util.un_uinst hd  in
                uu____451.FStar_Syntax_Syntax.n  in
              (uu____450, args)  in
            (match uu____435 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(tactic,FStar_Pervasives_Native.None )::(assertion,FStar_Pervasives_Native.None
                                                            )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol1 with
                  | Pos  ->
                      let uu____513 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____513 with
                       | (gs,uu____521) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____528 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____528 with
                       | (gs,uu____536) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol1 with
                  | Pos  ->
                      let uu____579 =
                        let uu____586 =
                          let uu____589 =
                            let uu____590 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____590
                             in
                          [uu____589]  in
                        (FStar_Syntax_Util.t_true, uu____586)  in
                      Simplified uu____579
                  | Both  ->
                      let uu____601 =
                        let uu____610 =
                          let uu____613 =
                            let uu____614 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____614
                             in
                          [uu____613]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____610)  in
                      Dual uu____601
                  | Neg  -> Simplified (assertion, []))
             | uu____627 -> Unchanged t)
  
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___0_719  ->
      match uu___0_719 with
      | Unchanged t -> let uu____725 = f t  in Unchanged uu____725
      | Simplified (t,gs) ->
          let uu____732 = let uu____739 = f t  in (uu____739, gs)  in
          Simplified uu____732
      | Dual (tn,tp,gs) ->
          let uu____749 =
            let uu____758 = f tn  in
            let uu____759 = f tp  in (uu____758, uu____759, gs)  in
          Dual uu____749
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____823 = f t1 t2  in Unchanged uu____823
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____835 = let uu____842 = f t1 t2  in (uu____842, gs)  in
            Simplified uu____835
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____856 = let uu____863 = f t1 t2  in (uu____863, gs)  in
            Simplified uu____856
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____882 =
              let uu____889 = f t1 t2  in
              (uu____889, (FStar_List.append gs1 gs2))  in
            Simplified uu____882
        | uu____892 ->
            let uu____901 = explode x  in
            (match uu____901 with
             | (n1,p1,gs1) ->
                 let uu____919 = explode y  in
                 (match uu____919 with
                  | (n2,p2,gs2) ->
                      let uu____937 =
                        let uu____946 = f n1 n2  in
                        let uu____947 = f p1 p2  in
                        (uu____946, uu____947, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____937))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd::tl ->
          let uu____1020 = comb2 (fun l  -> fun r  -> l :: r) hd acc  in
          aux tl uu____1020
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____1069  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol1  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____1112 =
              let uu____1113 = FStar_Syntax_Subst.compress t  in
              uu____1113.FStar_Syntax_Syntax.n  in
            match uu____1112 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol1 e t1  in
                let uu____1125 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____1125 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol1 e t1  in
                let uu____1151 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____1151 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____1171;
                   FStar_Syntax_Syntax.vars = uu____1172;_},(p,uu____1174)::
                 (q,uu____1176)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let r1 = traverse f (flip pol1) e p  in
                let r2 =
                  let uu____1234 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol1 uu____1234 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____1248 = FStar_Syntax_Util.mk_imp l r  in
                       uu____1248.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____1252;
                   FStar_Syntax_Syntax.vars = uu____1253;_},(p,uu____1255)::
                 (q,uu____1257)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let xq =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q
                   in
                let r1 =
                  let uu____1315 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____1315 p  in
                let r2 =
                  let uu____1317 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____1317 q  in
                (match (r1, r2) with
                 | (Unchanged uu____1324,Unchanged uu____1325) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____1343 = FStar_Syntax_Util.mk_iff l r  in
                            uu____1343.FStar_Syntax_Syntax.n) r1 r2
                 | uu____1346 ->
                     let uu____1355 = explode r1  in
                     (match uu____1355 with
                      | (pn,pp,gs1) ->
                          let uu____1373 = explode r2  in
                          (match uu____1373 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____1394 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____1397 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____1394
                                   uu____1397
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd,args) ->
                let r0 = traverse f pol1 e hd  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____1461  ->
                       fun r  ->
                         match uu____1461 with
                         | (a,q) ->
                             let r' = traverse f pol1 e a  in
                             comb2
                               (fun a1  -> fun args1  -> (a1, q) :: args1) r'
                               r) args (tpure [])
                   in
                comb2
                  (fun hd1  ->
                     fun args1  -> FStar_Syntax_Syntax.Tm_app (hd1, args1))
                  r0 r1
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1613 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____1613 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____1653  ->
                            match uu____1653 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol1) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____1675 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___256_1707 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___256_1707.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___256_1707.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____1675 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol1 e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____1735 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____1735.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____1781 = traverse f pol1 e t1  in
                let uu____1786 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____1786 uu____1781
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____1861 = traverse f pol1 e sc  in
                let uu____1866 =
                  let uu____1885 =
                    FStar_List.map
                      (fun br  ->
                         let uu____1902 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____1902 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol1 e1 exp  in
                             let uu____1929 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____1929 r) brs
                     in
                  comb_list uu____1885  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____1861 uu____1866
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol1 e
                (let uu___288_2015 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___288_2015.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___288_2015.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____2022 =
                f pol1 e
                  (let uu___294_2026 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___294_2026.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___294_2026.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____2022
          | Dual (tn,tp,gs) ->
              let rp =
                f pol1 e
                  (let uu___301_2036 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___301_2036.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___301_2036.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____2037 = explode rp  in
              (match uu____2037 with
               | (uu____2046,p',gs') ->
                   Dual
                     ((let uu___308_2056 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___308_2056.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___308_2056.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
  
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant] e t
         in
      FStar_Syntax_Util.un_squash tn
  
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
        FStar_Options.optionstate) Prims.list)
  =
  fun env  ->
    fun goal  ->
      (let uu____2101 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg uu____2101);
      (let uu____2126 = FStar_ST.op_Bang FStar_Tactics_Interpreter.tacdbg  in
       if uu____2126
       then
         let uu____2150 =
           let uu____2152 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____2152
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____2155 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2150
           uu____2155
       else ());
      (let initial = (Prims.int_one, [])  in
       let uu____2190 =
         let uu____2199 = traverse by_tactic_interp Pos env goal  in
         match uu____2199 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____2223 ->
             failwith "preprocess: impossible, traverse returned a Dual"
          in
       match uu____2190 with
       | (t',gs) ->
           ((let uu____2252 =
               FStar_ST.op_Bang FStar_Tactics_Interpreter.tacdbg  in
             if uu____2252
             then
               let uu____2276 =
                 let uu____2278 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____2278
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____2281 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2276 uu____2281
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2336  ->
                    fun g  ->
                      match uu____2336 with
                      | (n,gs1) ->
                          let phi =
                            let uu____2385 =
                              let uu____2388 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____2389 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____2388 uu____2389  in
                            match uu____2385 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2390 =
                                  let uu____2396 =
                                    let uu____2398 =
                                      let uu____2400 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____2400
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____2398
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____2396)
                                   in
                                FStar_Errors.raise_error uu____2390
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____2405 =
                              FStar_ST.op_Bang
                                FStar_Tactics_Interpreter.tacdbg
                               in
                            if uu____2405
                            then
                              let uu____2429 = FStar_Util.string_of_int n  in
                              let uu____2431 =
                                let uu____2433 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____2433
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2429 uu____2431
                            else ());
                           (let label =
                              let uu____2439 =
                                let uu____2441 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____2441 = ""  in
                              if uu____2439
                              then
                                let uu____2447 = FStar_Util.string_of_int n
                                   in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____2447
                              else
                                (let uu____2452 =
                                   let uu____2454 =
                                     FStar_Util.string_of_int n  in
                                   let uu____2456 =
                                     let uu____2458 =
                                       let uu____2460 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.op_Hat uu____2460 ")"  in
                                     Prims.op_Hat " (" uu____2458  in
                                   Prims.op_Hat uu____2454 uu____2456  in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____2452)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____2466 =
                              let uu____2475 =
                                let uu____2482 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____2482, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____2475 :: gs1  in
                            ((n + Prims.int_one), uu____2466)))) s gs
                in
             let uu____2499 = s1  in
             match uu____2499 with
             | (uu____2521,gs1) ->
                 let gs2 = FStar_List.rev gs1  in
                 let uu____2556 =
                   let uu____2563 = FStar_Options.peek ()  in
                   (env, t', uu____2563)  in
                 uu____2556 :: gs2)))
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        if env.FStar_TypeChecker_Env.nosynth
        then
          let uu____2587 =
            let uu____2592 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____2593 =
              let uu____2594 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____2594]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____2592 uu____2593  in
          uu____2587 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____2622 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
              uu____2622);
           (let uu____2646 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____2646 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____2667 =
                        let uu____2670 = FStar_Tactics_Types.goal_env g  in
                        let uu____2671 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____2670 uu____2671  in
                      match uu____2667 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____2674 =
                              FStar_ST.op_Bang
                                FStar_Tactics_Interpreter.tacdbg
                               in
                            if uu____2674
                            then
                              let uu____2698 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____2698
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Common.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Common.deferred = [];
                                FStar_TypeChecker_Common.univ_ineqs =
                                  ([], []);
                                FStar_TypeChecker_Common.implicits = []
                              }  in
                            let uu____2713 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____2713 guard))
                      | FStar_Pervasives_Native.None  ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                              "synthesis left open goals")
                            typ.FStar_Syntax_Syntax.pos) gs;
                 w)))
  
let (solve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.implicits -> unit)
  =
  fun env  ->
    fun tau  ->
      fun imps  ->
        if env.FStar_TypeChecker_Env.nosynth
        then ()
        else
          ((let uu____2736 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
              uu____2736);
           (let gs =
              let uu____2763 = FStar_TypeChecker_Env.get_range env  in
              run_tactic_on_all_implicits tau.FStar_Syntax_Syntax.pos
                uu____2763 tau env imps
               in
            FStar_All.pipe_right gs
              (FStar_List.iter
                 (fun g  ->
                    let uu____2774 =
                      let uu____2777 = FStar_Tactics_Types.goal_env g  in
                      let uu____2778 = FStar_Tactics_Types.goal_type g  in
                      getprop uu____2777 uu____2778  in
                    match uu____2774 with
                    | FStar_Pervasives_Native.Some vc ->
                        ((let uu____2781 =
                            FStar_ST.op_Bang FStar_Tactics_Interpreter.tacdbg
                             in
                          if uu____2781
                          then
                            let uu____2805 =
                              FStar_Syntax_Print.term_to_string vc  in
                            FStar_Util.print1 "Synthesis left a goal: %s\n"
                              uu____2805
                          else ());
                         (let guard =
                            {
                              FStar_TypeChecker_Common.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Common.deferred = [];
                              FStar_TypeChecker_Common.univ_ineqs = ([], []);
                              FStar_TypeChecker_Common.implicits = []
                            }  in
                          let uu____2820 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____2820 guard))
                    | FStar_Pervasives_Native.None  ->
                        let uu____2821 = FStar_TypeChecker_Env.get_range env
                           in
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                            "synthesis left open goals") uu____2821))))
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun rng  ->
      fun tau  ->
        if env.FStar_TypeChecker_Env.nosynth
        then []
        else
          ((let uu____2848 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
              uu____2848);
           (let typ = FStar_Syntax_Syntax.t_decls  in
            let ps =
              FStar_Tactics_Basic.proofstate_of_goals
                tau.FStar_Syntax_Syntax.pos env [] []
               in
            let uu____2874 =
              let uu____2883 =
                FStar_Syntax_Embeddings.e_list
                  FStar_Reflection_Embeddings.e_sigelt
                 in
              FStar_Tactics_Interpreter.run_tactic_on_ps
                tau.FStar_Syntax_Syntax.pos tau.FStar_Syntax_Syntax.pos
                FStar_Syntax_Embeddings.e_unit () uu____2883 tau ps
               in
            match uu____2874 with
            | (gs,sigelts) ->
                ((let uu____2903 =
                    FStar_List.existsML
                      (fun g  ->
                         let uu____2908 =
                           let uu____2910 =
                             let uu____2913 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____2914 = FStar_Tactics_Types.goal_type g
                                in
                             getprop uu____2913 uu____2914  in
                           FStar_Option.isSome uu____2910  in
                         Prims.op_Negation uu____2908) gs
                     in
                  if uu____2903
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                        "splice left open goals") typ.FStar_Syntax_Syntax.pos
                  else ());
                 (let uu____2921 =
                    FStar_ST.op_Bang FStar_Tactics_Interpreter.tacdbg  in
                  if uu____2921
                  then
                    let uu____2945 =
                      FStar_Common.string_of_list
                        FStar_Syntax_Print.sigelt_to_string sigelts
                       in
                    FStar_Util.print1 "splice: got decls = %s\n" uu____2945
                  else ());
                 (let sigelts1 =
                    FStar_List.map
                      (fun se  ->
                         let uu___396_2956 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___396_2956.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng = rng;
                           FStar_Syntax_Syntax.sigquals =
                             (uu___396_2956.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___396_2956.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___396_2956.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___396_2956.FStar_Syntax_Syntax.sigopts)
                         }) sigelts
                     in
                  sigelts1))))
  
let (mpreprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun tau  ->
      fun tm  ->
        if env.FStar_TypeChecker_Env.nosynth
        then tm
        else
          ((let uu____2977 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
              uu____2977);
           (let ps =
              FStar_Tactics_Basic.proofstate_of_goals
                tm.FStar_Syntax_Syntax.pos env [] []
               in
            let uu____3002 =
              FStar_Tactics_Interpreter.run_tactic_on_ps
                tau.FStar_Syntax_Syntax.pos tm.FStar_Syntax_Syntax.pos
                FStar_Reflection_Embeddings.e_term tm
                FStar_Reflection_Embeddings.e_term tau ps
               in
            match uu____3002 with | (gs,tm1) -> tm1))
  
let (postprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun tau  ->
      fun typ  ->
        fun tm  ->
          if env.FStar_TypeChecker_Env.nosynth
          then tm
          else
            ((let uu____3040 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
                uu____3040);
             (let uu____3064 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None
                 in
              match uu____3064 with
              | (uvtm,uu____3083,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____3101 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero
                      uu____3101
                     in
                  let uu____3102 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____3102 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____3123 =
                               let uu____3126 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____3127 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____3126 uu____3127  in
                             match uu____3123 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____3130 =
                                     FStar_ST.op_Bang
                                       FStar_Tactics_Interpreter.tacdbg
                                      in
                                   if uu____3130
                                   then
                                     let uu____3154 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____3154
                                   else ());
                                  (let guard =
                                     {
                                       FStar_TypeChecker_Common.guard_f =
                                         (FStar_TypeChecker_Common.NonTrivial
                                            vc);
                                       FStar_TypeChecker_Common.deferred = [];
                                       FStar_TypeChecker_Common.univ_ineqs =
                                         ([], []);
                                       FStar_TypeChecker_Common.implicits =
                                         []
                                     }  in
                                   let uu____3169 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____3169 guard))
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Errors.raise_error
                                   (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                                     "postprocessing left open goals")
                                   typ.FStar_Syntax_Syntax.pos) gs;
                        (let g_imp1 =
                           FStar_TypeChecker_Rel.resolve_implicits_tac env
                             g_imp
                            in
                         FStar_Tactics_Interpreter.report_implicits
                           tm.FStar_Syntax_Syntax.pos
                           g_imp1.FStar_TypeChecker_Common.implicits;
                         uvtm)))))
  