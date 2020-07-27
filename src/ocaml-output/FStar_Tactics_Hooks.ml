open Prims
let (run_tactic_on_typ :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term ->
            (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term))
  =
  fun rng_tac ->
    fun rng_goal ->
      fun tactic ->
        fun env ->
          fun typ ->
            let rng =
              let uu____38 = FStar_Range.use_range rng_goal in
              let uu____39 = FStar_Range.use_range rng_tac in
              FStar_Range.range_of_rng uu____38 uu____39 in
            let uu____40 =
              FStar_Tactics_Basic.proofstate_of_goal_ty rng env typ in
            match uu____40 with
            | (ps, w) ->
                let uu____53 =
                  FStar_Tactics_Interpreter.run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic ps in
                (match uu____53 with | (gs, _res) -> (gs, w))
let (run_tactic_on_all_implicits :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_TypeChecker_Env.implicits ->
            FStar_Tactics_Types.goal Prims.list)
  =
  fun rng_tac ->
    fun rng_goal ->
      fun tactic ->
        fun env ->
          fun imps ->
            let uu____103 =
              FStar_Tactics_Basic.proofstate_of_all_implicits rng_goal env
                imps in
            match uu____103 with
            | (ps, uu____111) ->
                let uu____112 =
                  FStar_Tactics_Interpreter.run_tactic_on_ps rng_tac rng_goal
                    FStar_Syntax_Embeddings.e_unit ()
                    FStar_Syntax_Embeddings.e_unit tactic ps in
                (match uu____112 with | (goals, ()) -> goals)
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee -> match projectee with | Pos -> true | uu____131 -> false
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee -> match projectee with | Neg -> true | uu____137 -> false
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee -> match projectee with | Both -> true | uu____143 -> false
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Unchanged _0 -> true | uu____198 -> false
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee -> match projectee with | Unchanged _0 -> _0
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Simplified _0 -> true | uu____237 -> false
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee -> match projectee with | Simplified _0 -> _0
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Dual _0 -> true | uu____290 -> false
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee -> match projectee with | Dual _0 -> _0
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'uuuuuu330 . 'uuuuuu330 -> 'uuuuuu330 tres_m =
  fun x -> Unchanged x
let (flip : pol -> pol) =
  fun p -> match p with | Pos -> Neg | Neg -> Pos | Both -> Both
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol1 ->
    fun e ->
      fun t ->
        let uu____358 = FStar_Syntax_Util.head_and_args t in
        match uu____358 with
        | (hd, args) ->
            let uu____401 =
              let uu____416 =
                let uu____417 = FStar_Syntax_Util.un_uinst hd in
                uu____417.FStar_Syntax_Syntax.n in
              (uu____416, args) in
            (match uu____401 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (tactic, FStar_Pervasives_Native.None)::(assertion,
                                                         FStar_Pervasives_Native.None)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol1 with
                  | Pos ->
                      let uu____479 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion in
                      (match uu____479 with
                       | (gs, uu____487) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both ->
                      let uu____494 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion in
                      (match uu____494 with
                       | (gs, uu____502) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (assertion, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol1 with
                  | Pos ->
                      let uu____545 =
                        let uu____552 =
                          let uu____555 =
                            let uu____556 =
                              FStar_Tactics_Types.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____556 in
                          [uu____555] in
                        (FStar_Syntax_Util.t_true, uu____552) in
                      Simplified uu____545
                  | Both ->
                      let uu____567 =
                        let uu____576 =
                          let uu____579 =
                            let uu____580 =
                              FStar_Tactics_Types.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____580 in
                          [uu____579] in
                        (assertion, FStar_Syntax_Util.t_true, uu____576) in
                      Dual uu____567
                  | Neg -> Simplified (assertion, []))
             | uu____593 -> Unchanged t)
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1, gs) -> (t1, t1, gs)
    | Dual (tn, tp, gs) -> (tn, tp, gs)
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f ->
    fun uu___0_683 ->
      match uu___0_683 with
      | Unchanged t -> let uu____689 = f t in Unchanged uu____689
      | Simplified (t, gs) ->
          let uu____696 = let uu____703 = f t in (uu____703, gs) in
          Simplified uu____696
      | Dual (tn, tp, gs) ->
          let uu____713 =
            let uu____722 = f tn in
            let uu____723 = f tp in (uu____722, uu____723, gs) in
          Dual uu____713
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f ->
    fun x ->
      fun y ->
        match (x, y) with
        | (Unchanged t1, Unchanged t2) ->
            let uu____786 = f t1 t2 in Unchanged uu____786
        | (Unchanged t1, Simplified (t2, gs)) ->
            let uu____798 = let uu____805 = f t1 t2 in (uu____805, gs) in
            Simplified uu____798
        | (Simplified (t1, gs), Unchanged t2) ->
            let uu____819 = let uu____826 = f t1 t2 in (uu____826, gs) in
            Simplified uu____819
        | (Simplified (t1, gs1), Simplified (t2, gs2)) ->
            let uu____845 =
              let uu____852 = f t1 t2 in
              (uu____852, (FStar_List.append gs1 gs2)) in
            Simplified uu____845
        | uu____855 ->
            let uu____864 = explode x in
            (match uu____864 with
             | (n1, p1, gs1) ->
                 let uu____882 = explode y in
                 (match uu____882 with
                  | (n2, p2, gs2) ->
                      let uu____900 =
                        let uu____909 = f n1 n2 in
                        let uu____910 = f p1 p2 in
                        (uu____909, uu____910, (FStar_List.append gs1 gs2)) in
                      Dual uu____900))
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd::tl ->
          let uu____982 = comb2 (fun l -> fun r -> l :: r) hd acc in
          aux tl uu____982 in
    aux (FStar_List.rev rs) (tpure [])
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs ->
    fun m -> comb2 (fun uu____1030 -> fun x -> x) (Simplified ((), gs)) m
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f ->
    fun pol1 ->
      fun e ->
        fun t ->
          let r =
            let uu____1072 =
              let uu____1073 = FStar_Syntax_Subst.compress t in
              uu____1073.FStar_Syntax_Syntax.n in
            match uu____1072 with
            | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
                let tr = traverse f pol1 e t1 in
                let uu____1085 =
                  comb1 (fun t' -> FStar_Syntax_Syntax.Tm_uinst (t', us)) in
                uu____1085 tr
            | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
                let tr = traverse f pol1 e t1 in
                let uu____1111 =
                  comb1 (fun t' -> FStar_Syntax_Syntax.Tm_meta (t', m)) in
                uu____1111 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____1131;
                   FStar_Syntax_Syntax.vars = uu____1132;_},
                 (p, uu____1134)::(q, uu____1136)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let r1 = traverse f (flip pol1) e p in
                let r2 =
                  let uu____1194 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f pol1 uu____1194 q in
                comb2
                  (fun l ->
                     fun r ->
                       let uu____1208 = FStar_Syntax_Util.mk_imp l r in
                       uu____1208.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____1212;
                   FStar_Syntax_Syntax.vars = uu____1213;_},
                 (p, uu____1215)::(q, uu____1217)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let xq =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q in
                let r1 =
                  let uu____1275 = FStar_TypeChecker_Env.push_bv e xq in
                  traverse f Both uu____1275 p in
                let r2 =
                  let uu____1277 = FStar_TypeChecker_Env.push_bv e xp in
                  traverse f Both uu____1277 q in
                (match (r1, r2) with
                 | (Unchanged uu____1284, Unchanged uu____1285) ->
                     comb2
                       (fun l ->
                          fun r ->
                            let uu____1303 = FStar_Syntax_Util.mk_iff l r in
                            uu____1303.FStar_Syntax_Syntax.n) r1 r2
                 | uu____1306 ->
                     let uu____1315 = explode r1 in
                     (match uu____1315 with
                      | (pn, pp, gs1) ->
                          let uu____1333 = explode r2 in
                          (match uu____1333 with
                           | (qn, qp, gs2) ->
                               let t1 =
                                 let uu____1354 =
                                   FStar_Syntax_Util.mk_imp pn qp in
                                 let uu____1357 =
                                   FStar_Syntax_Util.mk_imp qn pp in
                                 FStar_Syntax_Util.mk_conj uu____1354
                                   uu____1357 in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd, args) ->
                let r0 = traverse f pol1 e hd in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____1421 ->
                       fun r ->
                         match uu____1421 with
                         | (a, q) ->
                             let r' = traverse f pol1 e a in
                             comb2 (fun a1 -> fun args1 -> (a1, q) :: args1)
                               r' r) args (tpure []) in
                comb2
                  (fun hd1 ->
                     fun args1 -> FStar_Syntax_Syntax.Tm_app (hd1, args1)) r0
                  r1
            | FStar_Syntax_Syntax.Tm_abs (bs, t1, k) ->
                let uu____1573 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____1573 with
                 | (bs1, topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let r0 =
                       FStar_List.map
                         (fun uu____1613 ->
                            match uu____1613 with
                            | (bv, aq) ->
                                let r =
                                  traverse f (flip pol1) e
                                    bv.FStar_Syntax_Syntax.sort in
                                let uu____1635 =
                                  comb1
                                    (fun s' ->
                                       ((let uu___256_1667 = bv in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___256_1667.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___256_1667.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq)) in
                                uu____1635 r) bs1 in
                     let rbs = comb_list r0 in
                     let rt = traverse f pol1 e' topen in
                     comb2
                       (fun bs2 ->
                          fun t2 ->
                            let uu____1695 = FStar_Syntax_Util.abs bs2 t2 k in
                            uu____1695.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, ef) ->
                let uu____1741 = traverse f pol1 e t1 in
                let uu____1746 =
                  comb1
                    (fun t2 -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef)) in
                uu____1746 uu____1741
            | FStar_Syntax_Syntax.Tm_match (sc, brs) ->
                let uu____1821 = traverse f pol1 e sc in
                let uu____1826 =
                  let uu____1845 =
                    FStar_List.map
                      (fun br ->
                         let uu____1862 = FStar_Syntax_Subst.open_branch br in
                         match uu____1862 with
                         | (pat, w, exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs in
                             let r = traverse f pol1 e1 exp in
                             let uu____1889 =
                               comb1
                                 (fun exp1 ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1)) in
                             uu____1889 r) brs in
                  comb_list uu____1845 in
                comb2
                  (fun sc1 ->
                     fun brs1 -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____1821 uu____1826
            | x -> tpure x in
          match r with
          | Unchanged tn' ->
              f pol1 e
                (let uu___288_1975 = t in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___288_1975.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___288_1975.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn', gs) ->
              let uu____1982 =
                f pol1 e
                  (let uu___294_1986 = t in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___294_1986.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___294_1986.FStar_Syntax_Syntax.vars)
                   }) in
              emit gs uu____1982
          | Dual (tn, tp, gs) ->
              let rp =
                f pol1 e
                  (let uu___301_1996 = t in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___301_1996.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___301_1996.FStar_Syntax_Syntax.vars)
                   }) in
              let uu____1997 = explode rp in
              (match uu____1997 with
               | (uu____2006, p', gs') ->
                   Dual
                     ((let uu___308_2016 = t in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___308_2016.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___308_2016.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    fun t ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant] e t in
      FStar_Syntax_Util.un_squash tn
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
        FStar_Options.optionstate) Prims.list)
  =
  fun env ->
    fun goal ->
      (let uu____2059 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg uu____2059);
      (let uu____2067 = FStar_ST.op_Bang FStar_Tactics_Interpreter.tacdbg in
       if uu____2067
       then
         let uu____2074 =
           let uu____2075 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____2075
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____2076 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2074
           uu____2076
       else ());
      (let initial = (Prims.int_one, []) in
       let uu____2105 =
         let uu____2114 = traverse by_tactic_interp Pos env goal in
         match uu____2114 with
         | Unchanged t' -> (t', [])
         | Simplified (t', gs) -> (t', gs)
         | uu____2138 ->
             failwith "preprocess: impossible, traverse returned a Dual" in
       match uu____2105 with
       | (t', gs) ->
           ((let uu____2166 =
               FStar_ST.op_Bang FStar_Tactics_Interpreter.tacdbg in
             if uu____2166
             then
               let uu____2173 =
                 let uu____2174 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2174
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2175 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2173 uu____2175
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2224 ->
                    fun g ->
                      match uu____2224 with
                      | (n, gs1) ->
                          let phi =
                            let uu____2269 =
                              let uu____2272 = FStar_Tactics_Types.goal_env g in
                              let uu____2273 =
                                FStar_Tactics_Types.goal_type g in
                              getprop uu____2272 uu____2273 in
                            match uu____2269 with
                            | FStar_Pervasives_Native.None ->
                                let uu____2274 =
                                  let uu____2279 =
                                    let uu____2280 =
                                      let uu____2281 =
                                        FStar_Tactics_Types.goal_type g in
                                      FStar_Syntax_Print.term_to_string
                                        uu____2281 in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____2280 in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____2279) in
                                FStar_Errors.raise_error uu____2274
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____2284 =
                              FStar_ST.op_Bang
                                FStar_Tactics_Interpreter.tacdbg in
                            if uu____2284
                            then
                              let uu____2291 = FStar_Util.string_of_int n in
                              let uu____2292 =
                                let uu____2293 =
                                  FStar_Tactics_Types.goal_type g in
                                FStar_Syntax_Print.term_to_string uu____2293 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2291 uu____2292
                            else ());
                           (let label =
                              let uu____2296 =
                                let uu____2297 =
                                  FStar_Tactics_Types.get_label g in
                                uu____2297 = "" in
                              if uu____2296
                              then
                                let uu____2298 = FStar_Util.string_of_int n in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____2298
                              else
                                (let uu____2300 =
                                   let uu____2301 =
                                     FStar_Util.string_of_int n in
                                   let uu____2302 =
                                     let uu____2303 =
                                       let uu____2304 =
                                         FStar_Tactics_Types.get_label g in
                                       Prims.op_Hat uu____2304 ")" in
                                     Prims.op_Hat " (" uu____2303 in
                                   Prims.op_Hat uu____2301 uu____2302 in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____2300) in
                            let gt' =
                              FStar_TypeChecker_Util.label label
                                goal.FStar_Syntax_Syntax.pos phi in
                            let uu____2306 =
                              let uu____2315 =
                                let uu____2322 =
                                  FStar_Tactics_Types.goal_env g in
                                (uu____2322, gt',
                                  (g.FStar_Tactics_Types.opts)) in
                              uu____2315 :: gs1 in
                            ((n + Prims.int_one), uu____2306)))) s gs in
             let uu____2337 = s1 in
             match uu____2337 with
             | (uu____2358, gs1) ->
                 let gs2 = FStar_List.rev gs1 in
                 let uu____2391 =
                   let uu____2398 = FStar_Options.peek () in
                   (env, t', uu____2398) in
                 uu____2391 :: gs2)))
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun typ ->
      fun tau ->
        if env.FStar_TypeChecker_Env.nosynth
        then
          let uu____2420 =
            FStar_TypeChecker_Util.fvar_const env
              FStar_Parser_Const.magic_lid in
          let uu____2421 =
            let uu____2422 =
              FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
            [uu____2422] in
          FStar_Syntax_Syntax.mk_Tm_app uu____2420 uu____2421
            typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____2449 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
            FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
              uu____2449);
           (let uu____2456 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ in
            match uu____2456 with
            | (gs, w) ->
                (FStar_List.iter
                   (fun g ->
                      let uu____2477 =
                        let uu____2480 = FStar_Tactics_Types.goal_env g in
                        let uu____2481 = FStar_Tactics_Types.goal_type g in
                        getprop uu____2480 uu____2481 in
                      match uu____2477 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____2484 =
                              FStar_ST.op_Bang
                                FStar_Tactics_Interpreter.tacdbg in
                            if uu____2484
                            then
                              let uu____2491 =
                                FStar_Syntax_Print.term_to_string vc in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____2491
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Common.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Common.deferred_to_tac = [];
                                FStar_TypeChecker_Common.deferred = [];
                                FStar_TypeChecker_Common.univ_ineqs =
                                  ([], []);
                                FStar_TypeChecker_Common.implicits = []
                              } in
                            let uu____2506 = FStar_Tactics_Types.goal_env g in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____2506 guard))
                      | FStar_Pervasives_Native.None ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                              "synthesis left open goals")
                            typ.FStar_Syntax_Syntax.pos) gs;
                 w)))
let (solve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.implicits -> unit)
  =
  fun env ->
    fun tau ->
      fun imps ->
        if env.FStar_TypeChecker_Env.nosynth
        then ()
        else
          ((let uu____2524 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
            FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
              uu____2524);
           (let gs =
              let uu____2534 = FStar_TypeChecker_Env.get_range env in
              run_tactic_on_all_implicits tau.FStar_Syntax_Syntax.pos
                uu____2534 tau env imps in
            FStar_All.pipe_right gs
              (FStar_List.iter
                 (fun g ->
                    let uu____2545 =
                      let uu____2548 = FStar_Tactics_Types.goal_env g in
                      let uu____2549 = FStar_Tactics_Types.goal_type g in
                      getprop uu____2548 uu____2549 in
                    match uu____2545 with
                    | FStar_Pervasives_Native.Some vc ->
                        ((let uu____2552 =
                            FStar_ST.op_Bang FStar_Tactics_Interpreter.tacdbg in
                          if uu____2552
                          then
                            let uu____2559 =
                              FStar_Syntax_Print.term_to_string vc in
                            FStar_Util.print1 "Synthesis left a goal: %s\n"
                              uu____2559
                          else ());
                         (let guard =
                            {
                              FStar_TypeChecker_Common.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Common.deferred_to_tac = [];
                              FStar_TypeChecker_Common.deferred = [];
                              FStar_TypeChecker_Common.univ_ineqs = ([], []);
                              FStar_TypeChecker_Common.implicits = []
                            } in
                          let uu____2574 = FStar_Tactics_Types.goal_env g in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____2574 guard))
                    | FStar_Pervasives_Native.None ->
                        let uu____2575 = FStar_TypeChecker_Env.get_range env in
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                            "synthesis left open goals") uu____2575))))
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env ->
    fun rng ->
      fun tau ->
        if env.FStar_TypeChecker_Env.nosynth
        then []
        else
          ((let uu____2597 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
            FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
              uu____2597);
           (let typ = FStar_Syntax_Syntax.t_decls in
            let ps =
              FStar_Tactics_Basic.proofstate_of_goals
                tau.FStar_Syntax_Syntax.pos env [] [] in
            let uu____2606 =
              let uu____2615 =
                FStar_Syntax_Embeddings.e_list
                  FStar_Reflection_Embeddings.e_sigelt in
              FStar_Tactics_Interpreter.run_tactic_on_ps
                tau.FStar_Syntax_Syntax.pos tau.FStar_Syntax_Syntax.pos
                FStar_Syntax_Embeddings.e_unit () uu____2615 tau ps in
            match uu____2606 with
            | (gs, sigelts) ->
                ((let uu____2635 =
                    FStar_List.existsML
                      (fun g ->
                         let uu____2639 =
                           let uu____2640 =
                             let uu____2643 = FStar_Tactics_Types.goal_env g in
                             let uu____2644 = FStar_Tactics_Types.goal_type g in
                             getprop uu____2643 uu____2644 in
                           FStar_Option.isSome uu____2640 in
                         Prims.op_Negation uu____2639) gs in
                  if uu____2635
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                        "splice left open goals") typ.FStar_Syntax_Syntax.pos
                  else ());
                 (let uu____2647 =
                    FStar_ST.op_Bang FStar_Tactics_Interpreter.tacdbg in
                  if uu____2647
                  then
                    let uu____2654 =
                      FStar_Common.string_of_list
                        FStar_Syntax_Print.sigelt_to_string sigelts in
                    FStar_Util.print1 "splice: got decls = %s\n" uu____2654
                  else ());
                 (let sigelts1 =
                    FStar_List.map
                      (fun se ->
                         let uu___396_2662 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___396_2662.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng = rng;
                           FStar_Syntax_Syntax.sigquals =
                             (uu___396_2662.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___396_2662.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___396_2662.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___396_2662.FStar_Syntax_Syntax.sigopts)
                         }) sigelts in
                  sigelts1))))
let (mpreprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun tau ->
      fun tm ->
        if env.FStar_TypeChecker_Env.nosynth
        then tm
        else
          ((let uu____2680 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
            FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
              uu____2680);
           (let ps =
              FStar_Tactics_Basic.proofstate_of_goals
                tm.FStar_Syntax_Syntax.pos env [] [] in
            let uu____2688 =
              FStar_Tactics_Interpreter.run_tactic_on_ps
                tau.FStar_Syntax_Syntax.pos tm.FStar_Syntax_Syntax.pos
                FStar_Reflection_Embeddings.e_term tm
                FStar_Reflection_Embeddings.e_term tau ps in
            match uu____2688 with | (gs, tm1) -> tm1))
let (postprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun tau ->
      fun typ ->
        fun tm ->
          if env.FStar_TypeChecker_Env.nosynth
          then tm
          else
            ((let uu____2723 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
              FStar_ST.op_Colon_Equals FStar_Tactics_Interpreter.tacdbg
                uu____2723);
             (let uu____2730 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None in
              match uu____2730 with
              | (uvtm, uu____2744, g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ in
                  let goal =
                    let uu____2762 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm in
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero
                      uu____2762 in
                  let uu____2763 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal in
                  (match uu____2763 with
                   | (gs, w) ->
                       (FStar_List.iter
                          (fun g ->
                             let uu____2784 =
                               let uu____2787 =
                                 FStar_Tactics_Types.goal_env g in
                               let uu____2788 =
                                 FStar_Tactics_Types.goal_type g in
                               getprop uu____2787 uu____2788 in
                             match uu____2784 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____2791 =
                                     FStar_ST.op_Bang
                                       FStar_Tactics_Interpreter.tacdbg in
                                   if uu____2791
                                   then
                                     let uu____2798 =
                                       FStar_Syntax_Print.term_to_string vc in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____2798
                                   else ());
                                  (let guard =
                                     {
                                       FStar_TypeChecker_Common.guard_f =
                                         (FStar_TypeChecker_Common.NonTrivial
                                            vc);
                                       FStar_TypeChecker_Common.deferred_to_tac
                                         = [];
                                       FStar_TypeChecker_Common.deferred = [];
                                       FStar_TypeChecker_Common.univ_ineqs =
                                         ([], []);
                                       FStar_TypeChecker_Common.implicits =
                                         []
                                     } in
                                   let uu____2813 =
                                     FStar_Tactics_Types.goal_env g in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____2813 guard))
                             | FStar_Pervasives_Native.None ->
                                 FStar_Errors.raise_error
                                   (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                                     "postprocessing left open goals")
                                   typ.FStar_Syntax_Syntax.pos) gs;
                        (let g_imp1 =
                           FStar_TypeChecker_Rel.resolve_implicits_tac env
                             g_imp in
                         FStar_Tactics_Interpreter.report_implicits
                           tm.FStar_Syntax_Syntax.pos
                           g_imp1.FStar_TypeChecker_Common.implicits;
                         uvtm)))))