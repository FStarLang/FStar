open Prims
let (dbg_Tac : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Tac"
let (dbg_SpinoffAll : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "SpinoffAll"
let (run_tactic_on_typ :
  FStarC_Compiler_Range_Type.range ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_Syntax_Syntax.term ->
        FStarC_TypeChecker_Env.env ->
          FStarC_Syntax_Syntax.term ->
            (FStarC_Tactics_Types.goal Prims.list *
              FStarC_Syntax_Syntax.term))
  =
  fun rng_tac ->
    fun rng_goal ->
      fun tactic ->
        fun env ->
          fun typ ->
            let rng =
              let uu___ = FStarC_Compiler_Range_Type.use_range rng_tac in
              let uu___1 = FStarC_Compiler_Range_Type.use_range rng_goal in
              FStarC_Compiler_Range_Type.range_of_rng uu___ uu___1 in
            let uu___ =
              FStarC_Tactics_V2_Basic.proofstate_of_goal_ty rng env typ in
            match uu___ with
            | (ps, w) ->
                let tactic_already_typed = false in
                let uu___1 =
                  FStarC_Tactics_Interpreter.run_tactic_on_ps rng_tac
                    rng_goal false FStarC_Syntax_Embeddings.e_unit ()
                    FStarC_Syntax_Embeddings.e_unit tactic
                    tactic_already_typed ps in
                (match uu___1 with | (gs, _res) -> (gs, w))
let (run_tactic_on_all_implicits :
  FStarC_Compiler_Range_Type.range ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_Syntax_Syntax.term ->
        FStarC_TypeChecker_Env.env ->
          FStarC_TypeChecker_Env.implicits ->
            FStarC_Tactics_Types.goal Prims.list)
  =
  fun rng_tac ->
    fun rng_goal ->
      fun tactic ->
        fun env ->
          fun imps ->
            let uu___ =
              FStarC_Tactics_V2_Basic.proofstate_of_all_implicits rng_goal
                env imps in
            match uu___ with
            | (ps, uu___1) ->
                let tactic_already_typed = false in
                let uu___2 =
                  let uu___3 = FStarC_TypeChecker_Env.get_range env in
                  FStarC_Tactics_Interpreter.run_tactic_on_ps uu___3 rng_goal
                    true FStarC_Syntax_Embeddings.e_unit ()
                    FStarC_Syntax_Embeddings.e_unit tactic
                    tactic_already_typed ps in
                (match uu___2 with | (goals, ()) -> goals)
type pol =
  | StrictlyPositive 
  | Pos 
  | Neg 
  | Both 
let (uu___is_StrictlyPositive : pol -> Prims.bool) =
  fun projectee ->
    match projectee with | StrictlyPositive -> true | uu___ -> false
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee -> match projectee with | Pos -> true | uu___ -> false
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee -> match projectee with | Neg -> true | uu___ -> false
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee -> match projectee with | Both -> true | uu___ -> false
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStarC_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStarC_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Unchanged _0 -> true | uu___ -> false
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee -> match projectee with | Unchanged _0 -> _0
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee ->
    match projectee with | Simplified _0 -> true | uu___ -> false
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStarC_Tactics_Types.goal Prims.list) =
  fun projectee -> match projectee with | Simplified _0 -> _0
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee -> match projectee with | Dual _0 -> true | uu___ -> false
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStarC_Tactics_Types.goal Prims.list) =
  fun projectee -> match projectee with | Dual _0 -> _0
type tres = FStarC_Syntax_Syntax.term tres_m
let tpure : 'uuuuu . 'uuuuu -> 'uuuuu tres_m = fun x -> Unchanged x
let (flip : pol -> pol) =
  fun p ->
    match p with
    | StrictlyPositive -> Neg
    | Pos -> Neg
    | Neg -> Pos
    | Both -> Both
let (getprop :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    fun t ->
      let tn =
        FStarC_TypeChecker_Normalize.normalize
          [FStarC_TypeChecker_Env.Weak;
          FStarC_TypeChecker_Env.HNF;
          FStarC_TypeChecker_Env.UnfoldUntil
            FStarC_Syntax_Syntax.delta_constant] e t in
      FStarC_Syntax_Util.un_squash tn
let (by_tactic_interp :
  pol -> FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> tres) =
  fun pol1 ->
    fun e ->
      fun t ->
        let uu___ = FStarC_Syntax_Util.head_and_args t in
        match uu___ with
        | (hd, args) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                uu___3.FStarC_Syntax_Syntax.n in
              (uu___2, args) in
            (match uu___1 with
             | (FStarC_Syntax_Syntax.Tm_fvar fv,
                (tactic, FStar_Pervasives_Native.None)::(assertion,
                                                         FStar_Pervasives_Native.None)::[])
                 when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.by_tactic_lid
                 ->
                 (match pol1 with
                  | StrictlyPositive ->
                      let uu___2 =
                        run_tactic_on_typ tactic.FStarC_Syntax_Syntax.pos
                          assertion.FStarC_Syntax_Syntax.pos tactic e
                          assertion in
                      (match uu___2 with
                       | (gs, uu___3) ->
                           Simplified (FStarC_Syntax_Util.t_true, gs))
                  | Pos ->
                      let uu___2 =
                        run_tactic_on_typ tactic.FStarC_Syntax_Syntax.pos
                          assertion.FStarC_Syntax_Syntax.pos tactic e
                          assertion in
                      (match uu___2 with
                       | (gs, uu___3) ->
                           Simplified (FStarC_Syntax_Util.t_true, gs))
                  | Both ->
                      let uu___2 =
                        run_tactic_on_typ tactic.FStarC_Syntax_Syntax.pos
                          assertion.FStarC_Syntax_Syntax.pos tactic e
                          assertion in
                      (match uu___2 with
                       | (gs, uu___3) ->
                           Dual (assertion, FStarC_Syntax_Util.t_true, gs))
                  | Neg -> Simplified (assertion, []))
             | (FStarC_Syntax_Syntax.Tm_fvar fv,
                (assertion, FStar_Pervasives_Native.None)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.spinoff_lid
                 ->
                 (match pol1 with
                  | StrictlyPositive ->
                      let g =
                        let uu___2 =
                          FStarC_Tactics_Types.goal_of_goal_ty e assertion in
                        FStar_Pervasives_Native.fst uu___2 in
                      let g1 =
                        FStarC_Tactics_Types.set_label "spun-off assertion" g in
                      Simplified (FStarC_Syntax_Util.t_true, [g1])
                  | Pos ->
                      let g =
                        let uu___2 =
                          FStarC_Tactics_Types.goal_of_goal_ty e assertion in
                        FStar_Pervasives_Native.fst uu___2 in
                      let g1 =
                        FStarC_Tactics_Types.set_label "spun-off assertion" g in
                      Simplified (FStarC_Syntax_Util.t_true, [g1])
                  | Both ->
                      let g =
                        let uu___2 =
                          FStarC_Tactics_Types.goal_of_goal_ty e assertion in
                        FStar_Pervasives_Native.fst uu___2 in
                      let g1 =
                        FStarC_Tactics_Types.set_label "spun-off assertion" g in
                      Dual (assertion, FStarC_Syntax_Util.t_true, [g1])
                  | Neg -> Simplified (assertion, []))
             | (FStarC_Syntax_Syntax.Tm_fvar fv,
                (tactic, FStar_Pervasives_Native.None)::(typ,
                                                         FStar_Pervasives_Native.Some
                                                         {
                                                           FStarC_Syntax_Syntax.aqual_implicit
                                                             = true;
                                                           FStarC_Syntax_Syntax.aqual_attributes
                                                             = uu___2;_})::
                (tm, FStar_Pervasives_Native.None)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.rewrite_by_tactic_lid
                 ->
                 let uu___3 =
                   FStarC_TypeChecker_Env.new_implicit_var_aux
                     "rewrite_with_tactic RHS" tm.FStarC_Syntax_Syntax.pos e
                     typ FStarC_Syntax_Syntax.Strict
                     FStar_Pervasives_Native.None false in
                 (match uu___3 with
                  | (uvtm, uu___4, g_imp) ->
                      let u = e.FStarC_TypeChecker_Env.universe_of e typ in
                      let goal =
                        let uu___5 = FStarC_Syntax_Util.mk_eq2 u typ tm uvtm in
                        FStarC_Syntax_Util.mk_squash
                          FStarC_Syntax_Syntax.U_zero uu___5 in
                      let uu___5 =
                        run_tactic_on_typ tactic.FStarC_Syntax_Syntax.pos
                          tm.FStarC_Syntax_Syntax.pos tactic e goal in
                      (match uu___5 with
                       | (gs, uu___6) ->
                           let tagged_imps =
                             FStarC_TypeChecker_Rel.resolve_implicits_tac e
                               g_imp in
                           (FStarC_Tactics_Interpreter.report_implicits
                              tm.FStarC_Syntax_Syntax.pos tagged_imps;
                            Simplified (uvtm, gs))))
             | uu___2 -> Unchanged t)
let explode :
  'a . 'a tres_m -> ('a * 'a * FStarC_Tactics_Types.goal Prims.list) =
  fun t ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1, gs) -> (t1, t1, gs)
    | Dual (tn, tp, gs) -> (tn, tp, gs)
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f ->
    fun uu___ ->
      match uu___ with
      | Unchanged t -> let uu___1 = f t in Unchanged uu___1
      | Simplified (t, gs) ->
          let uu___1 = let uu___2 = f t in (uu___2, gs) in Simplified uu___1
      | Dual (tn, tp, gs) ->
          let uu___1 =
            let uu___2 = f tn in let uu___3 = f tp in (uu___2, uu___3, gs) in
          Dual uu___1
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f ->
    fun x ->
      fun y ->
        match (x, y) with
        | (Unchanged t1, Unchanged t2) ->
            let uu___ = f t1 t2 in Unchanged uu___
        | (Unchanged t1, Simplified (t2, gs)) ->
            let uu___ = let uu___1 = f t1 t2 in (uu___1, gs) in
            Simplified uu___
        | (Simplified (t1, gs), Unchanged t2) ->
            let uu___ = let uu___1 = f t1 t2 in (uu___1, gs) in
            Simplified uu___
        | (Simplified (t1, gs1), Simplified (t2, gs2)) ->
            let uu___ =
              let uu___1 = f t1 t2 in
              (uu___1, (FStarC_Compiler_List.op_At gs1 gs2)) in
            Simplified uu___
        | uu___ ->
            let uu___1 = explode x in
            (match uu___1 with
             | (n1, p1, gs1) ->
                 let uu___2 = explode y in
                 (match uu___2 with
                  | (n2, p2, gs2) ->
                      let uu___3 =
                        let uu___4 = f n1 n2 in
                        let uu___5 = f p1 p2 in
                        (uu___4, uu___5,
                          (FStarC_Compiler_List.op_At gs1 gs2)) in
                      Dual uu___3))
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd::tl ->
          let uu___ = comb2 (fun l -> fun r -> l :: r) hd acc in aux tl uu___ in
    aux (FStarC_Compiler_List.rev rs) (tpure [])
let emit :
  'a . FStarC_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m =
  fun gs -> fun m -> comb2 (fun uu___ -> fun x -> x) (Simplified ((), gs)) m
let rec (traverse :
  (pol -> FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> tres) ->
    pol -> FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> tres)
  =
  fun f ->
    fun pol1 ->
      fun e ->
        fun t ->
          let r =
            let uu___ =
              let uu___1 = FStarC_Syntax_Subst.compress t in
              uu___1.FStarC_Syntax_Syntax.n in
            match uu___ with
            | FStarC_Syntax_Syntax.Tm_uinst (t1, us) ->
                let tr = traverse f pol1 e t1 in
                let uu___1 =
                  comb1 (fun t' -> FStarC_Syntax_Syntax.Tm_uinst (t', us)) in
                uu___1 tr
            | FStarC_Syntax_Syntax.Tm_meta
                { FStarC_Syntax_Syntax.tm2 = t1;
                  FStarC_Syntax_Syntax.meta = m;_}
                ->
                let tr = traverse f pol1 e t1 in
                let uu___1 =
                  comb1
                    (fun t' ->
                       FStarC_Syntax_Syntax.Tm_meta
                         {
                           FStarC_Syntax_Syntax.tm2 = t';
                           FStarC_Syntax_Syntax.meta = m
                         }) in
                uu___1 tr
            | FStarC_Syntax_Syntax.Tm_app
                {
                  FStarC_Syntax_Syntax.hd =
                    {
                      FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar
                        fv;
                      FStarC_Syntax_Syntax.pos = uu___1;
                      FStarC_Syntax_Syntax.vars = uu___2;
                      FStarC_Syntax_Syntax.hash_code = uu___3;_};
                  FStarC_Syntax_Syntax.args = (p, uu___4)::(q, uu___5)::[];_}
                when
                FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.imp_lid
                ->
                let x =
                  FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let r1 = traverse f (flip pol1) e p in
                let r2 =
                  let uu___6 = FStarC_TypeChecker_Env.push_bv e x in
                  traverse f pol1 uu___6 q in
                comb2
                  (fun l ->
                     fun r3 ->
                       let uu___6 = FStarC_Syntax_Util.mk_imp l r3 in
                       uu___6.FStarC_Syntax_Syntax.n) r1 r2
            | FStarC_Syntax_Syntax.Tm_app
                {
                  FStarC_Syntax_Syntax.hd =
                    {
                      FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar
                        fv;
                      FStarC_Syntax_Syntax.pos = uu___1;
                      FStarC_Syntax_Syntax.vars = uu___2;
                      FStarC_Syntax_Syntax.hash_code = uu___3;_};
                  FStarC_Syntax_Syntax.args = (p, uu___4)::(q, uu___5)::[];_}
                when
                FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.iff_lid
                ->
                let xp =
                  FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let xq =
                  FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q in
                let r1 =
                  let uu___6 = FStarC_TypeChecker_Env.push_bv e xq in
                  traverse f Both uu___6 p in
                let r2 =
                  let uu___6 = FStarC_TypeChecker_Env.push_bv e xp in
                  traverse f Both uu___6 q in
                (match (r1, r2) with
                 | (Unchanged uu___6, Unchanged uu___7) ->
                     comb2
                       (fun l ->
                          fun r3 ->
                            let uu___8 = FStarC_Syntax_Util.mk_iff l r3 in
                            uu___8.FStarC_Syntax_Syntax.n) r1 r2
                 | uu___6 ->
                     let uu___7 = explode r1 in
                     (match uu___7 with
                      | (pn, pp, gs1) ->
                          let uu___8 = explode r2 in
                          (match uu___8 with
                           | (qn, qp, gs2) ->
                               let t1 =
                                 let uu___9 = FStarC_Syntax_Util.mk_imp pn qp in
                                 let uu___10 =
                                   FStarC_Syntax_Util.mk_imp qn pp in
                                 FStarC_Syntax_Util.mk_conj uu___9 uu___10 in
                               Simplified
                                 ((t1.FStarC_Syntax_Syntax.n),
                                   (FStarC_Compiler_List.op_At gs1 gs2)))))
            | FStarC_Syntax_Syntax.Tm_app
                { FStarC_Syntax_Syntax.hd = hd;
                  FStarC_Syntax_Syntax.args = args;_}
                ->
                let r0 = traverse f pol1 e hd in
                let r1 =
                  FStarC_Compiler_List.fold_right
                    (fun uu___1 ->
                       fun r2 ->
                         match uu___1 with
                         | (a, q) ->
                             let r' = traverse f pol1 e a in
                             comb2 (fun a1 -> fun args1 -> (a1, q) :: args1)
                               r' r2) args (tpure []) in
                comb2
                  (fun hd1 ->
                     fun args1 ->
                       FStarC_Syntax_Syntax.Tm_app
                         {
                           FStarC_Syntax_Syntax.hd = hd1;
                           FStarC_Syntax_Syntax.args = args1
                         }) r0 r1
            | FStarC_Syntax_Syntax.Tm_abs
                { FStarC_Syntax_Syntax.bs = bs;
                  FStarC_Syntax_Syntax.body = t1;
                  FStarC_Syntax_Syntax.rc_opt = k;_}
                ->
                let uu___1 = FStarC_Syntax_Subst.open_term bs t1 in
                (match uu___1 with
                 | (bs1, topen) ->
                     let e' = FStarC_TypeChecker_Env.push_binders e bs1 in
                     let r0 =
                       FStarC_Compiler_List.map
                         (fun b ->
                            let r1 =
                              traverse f (flip pol1) e
                                (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                            let uu___2 =
                              comb1
                                (fun s' ->
                                   {
                                     FStarC_Syntax_Syntax.binder_bv =
                                       (let uu___3 =
                                          b.FStarC_Syntax_Syntax.binder_bv in
                                        {
                                          FStarC_Syntax_Syntax.ppname =
                                            (uu___3.FStarC_Syntax_Syntax.ppname);
                                          FStarC_Syntax_Syntax.index =
                                            (uu___3.FStarC_Syntax_Syntax.index);
                                          FStarC_Syntax_Syntax.sort = s'
                                        });
                                     FStarC_Syntax_Syntax.binder_qual =
                                       (b.FStarC_Syntax_Syntax.binder_qual);
                                     FStarC_Syntax_Syntax.binder_positivity =
                                       (b.FStarC_Syntax_Syntax.binder_positivity);
                                     FStarC_Syntax_Syntax.binder_attrs =
                                       (b.FStarC_Syntax_Syntax.binder_attrs)
                                   }) in
                            uu___2 r1) bs1 in
                     let rbs = comb_list r0 in
                     let rt = traverse f pol1 e' topen in
                     comb2
                       (fun bs2 ->
                          fun t2 ->
                            let uu___2 = FStarC_Syntax_Util.abs bs2 t2 k in
                            uu___2.FStarC_Syntax_Syntax.n) rbs rt)
            | FStarC_Syntax_Syntax.Tm_ascribed
                { FStarC_Syntax_Syntax.tm = t1;
                  FStarC_Syntax_Syntax.asc = asc;
                  FStarC_Syntax_Syntax.eff_opt = ef;_}
                ->
                let uu___1 = traverse f pol1 e t1 in
                let uu___2 =
                  comb1
                    (fun t2 ->
                       FStarC_Syntax_Syntax.Tm_ascribed
                         {
                           FStarC_Syntax_Syntax.tm = t2;
                           FStarC_Syntax_Syntax.asc = asc;
                           FStarC_Syntax_Syntax.eff_opt = ef
                         }) in
                uu___2 uu___1
            | FStarC_Syntax_Syntax.Tm_match
                { FStarC_Syntax_Syntax.scrutinee = sc;
                  FStarC_Syntax_Syntax.ret_opt = asc_opt;
                  FStarC_Syntax_Syntax.brs = brs;
                  FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
                ->
                let uu___1 = traverse f pol1 e sc in
                let uu___2 =
                  let uu___3 =
                    FStarC_Compiler_List.map
                      (fun br ->
                         let uu___4 = FStarC_Syntax_Subst.open_branch br in
                         match uu___4 with
                         | (pat, w, exp) ->
                             let bvs = FStarC_Syntax_Syntax.pat_bvs pat in
                             let e1 = FStarC_TypeChecker_Env.push_bvs e bvs in
                             let r1 = traverse f pol1 e1 exp in
                             let uu___5 =
                               comb1
                                 (fun exp1 ->
                                    FStarC_Syntax_Subst.close_branch
                                      (pat, w, exp1)) in
                             uu___5 r1) brs in
                  comb_list uu___3 in
                comb2
                  (fun sc1 ->
                     fun brs1 ->
                       FStarC_Syntax_Syntax.Tm_match
                         {
                           FStarC_Syntax_Syntax.scrutinee = sc1;
                           FStarC_Syntax_Syntax.ret_opt = asc_opt;
                           FStarC_Syntax_Syntax.brs = brs1;
                           FStarC_Syntax_Syntax.rc_opt1 = lopt
                         }) uu___1 uu___2
            | x -> tpure x in
          match r with
          | Unchanged tn' ->
              f pol1 e
                {
                  FStarC_Syntax_Syntax.n = tn';
                  FStarC_Syntax_Syntax.pos = (t.FStarC_Syntax_Syntax.pos);
                  FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
                  FStarC_Syntax_Syntax.hash_code =
                    (t.FStarC_Syntax_Syntax.hash_code)
                }
          | Simplified (tn', gs) ->
              let uu___ =
                f pol1 e
                  {
                    FStarC_Syntax_Syntax.n = tn';
                    FStarC_Syntax_Syntax.pos = (t.FStarC_Syntax_Syntax.pos);
                    FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
                    FStarC_Syntax_Syntax.hash_code =
                      (t.FStarC_Syntax_Syntax.hash_code)
                  } in
              emit gs uu___
          | Dual (tn, tp, gs) ->
              let rp =
                f pol1 e
                  {
                    FStarC_Syntax_Syntax.n = tp;
                    FStarC_Syntax_Syntax.pos = (t.FStarC_Syntax_Syntax.pos);
                    FStarC_Syntax_Syntax.vars = (t.FStarC_Syntax_Syntax.vars);
                    FStarC_Syntax_Syntax.hash_code =
                      (t.FStarC_Syntax_Syntax.hash_code)
                  } in
              let uu___ = explode rp in
              (match uu___ with
               | (uu___1, p', gs') ->
                   Dual
                     ({
                        FStarC_Syntax_Syntax.n = tn;
                        FStarC_Syntax_Syntax.pos =
                          (t.FStarC_Syntax_Syntax.pos);
                        FStarC_Syntax_Syntax.vars =
                          (t.FStarC_Syntax_Syntax.vars);
                        FStarC_Syntax_Syntax.hash_code =
                          (t.FStarC_Syntax_Syntax.hash_code)
                      }, p', (FStarC_Compiler_List.op_At gs gs')))
let (preprocess :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      (Prims.bool * (FStarC_TypeChecker_Env.env * FStarC_Syntax_Syntax.term *
        FStarC_Options.optionstate) Prims.list))
  =
  fun env ->
    fun goal ->
      FStarC_Errors.with_ctx "While preprocessing VC with a tactic"
        (fun uu___ ->
           (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Tac in
            if uu___2
            then
              let uu___3 =
                let uu___4 = FStarC_TypeChecker_Env.all_binders env in
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_list
                     FStarC_Syntax_Print.showable_binder) uu___4 in
              let uu___4 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term goal in
              FStarC_Compiler_Util.print2 "About to preprocess %s |= %s\n"
                uu___3 uu___4
            else ());
           (let initial = (Prims.int_one, []) in
            let uu___2 =
              let uu___3 = traverse by_tactic_interp Pos env goal in
              match uu___3 with
              | Unchanged t' -> (false, (t', []))
              | Simplified (t', gs) -> (true, (t', gs))
              | uu___4 ->
                  failwith "preprocess: impossible, traverse returned a Dual" in
            match uu___2 with
            | (did_anything, (t', gs)) ->
                ((let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Tac in
                  if uu___4
                  then
                    let uu___5 =
                      let uu___6 = FStarC_TypeChecker_Env.all_binders env in
                      FStarC_Class_Show.show
                        (FStarC_Class_Show.show_list
                           FStarC_Syntax_Print.showable_binder) uu___6 in
                    let uu___6 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term t' in
                    FStarC_Compiler_Util.print2
                      "Main goal simplified to: %s |- %s\n" uu___5 uu___6
                  else ());
                 (let s = initial in
                  let s1 =
                    FStarC_Compiler_List.fold_left
                      (fun uu___4 ->
                         fun g ->
                           match uu___4 with
                           | (n, gs1) ->
                               let phi =
                                 let uu___5 =
                                   let uu___6 =
                                     FStarC_Tactics_Types.goal_env g in
                                   let uu___7 =
                                     FStarC_Tactics_Types.goal_type g in
                                   getprop uu___6 uu___7 in
                                 match uu___5 with
                                 | FStar_Pervasives_Native.None ->
                                     let uu___6 =
                                       let uu___7 =
                                         let uu___8 =
                                           FStarC_Tactics_Types.goal_type g in
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Print.showable_term
                                           uu___8 in
                                       FStarC_Compiler_Util.format1
                                         "Tactic returned proof-relevant goal: %s"
                                         uu___7 in
                                     FStarC_Errors.raise_error
                                       FStarC_TypeChecker_Env.hasRange_env
                                       env
                                       FStarC_Errors_Codes.Fatal_TacticProofRelevantGoal
                                       ()
                                       (Obj.magic
                                          FStarC_Errors_Msg.is_error_message_string)
                                       (Obj.magic uu___6)
                                 | FStar_Pervasives_Native.Some phi1 -> phi1 in
                               ((let uu___6 =
                                   FStarC_Compiler_Effect.op_Bang dbg_Tac in
                                 if uu___6
                                 then
                                   let uu___7 =
                                     FStarC_Class_Show.show
                                       FStarC_Class_Show.showable_int n in
                                   let uu___8 =
                                     let uu___9 =
                                       FStarC_Tactics_Types.goal_type g in
                                     FStarC_Class_Show.show
                                       FStarC_Syntax_Print.showable_term
                                       uu___9 in
                                   FStarC_Compiler_Util.print2
                                     "Got goal #%s: %s\n" uu___7 uu___8
                                 else ());
                                (let label =
                                   let uu___6 =
                                     let uu___7 =
                                       FStarC_Pprint.doc_of_string
                                         "Could not prove goal #" in
                                     let uu___8 =
                                       let uu___9 =
                                         FStarC_Class_PP.pp
                                           FStarC_Class_PP.pp_int n in
                                       let uu___10 =
                                         let uu___11 =
                                           let uu___12 =
                                             FStarC_Tactics_Types.get_label g in
                                           uu___12 = "" in
                                         if uu___11
                                         then FStarC_Pprint.empty
                                         else
                                           (let uu___13 =
                                              let uu___14 =
                                                FStarC_Tactics_Types.get_label
                                                  g in
                                              FStarC_Pprint.doc_of_string
                                                uu___14 in
                                            FStarC_Pprint.parens uu___13) in
                                       FStarC_Pprint.op_Hat_Slash_Hat uu___9
                                         uu___10 in
                                     FStarC_Pprint.op_Hat_Hat uu___7 uu___8 in
                                   [uu___6] in
                                 let gt' =
                                   let uu___6 =
                                     FStarC_Tactics_Types.goal_range g in
                                   FStarC_TypeChecker_Util.label label uu___6
                                     phi in
                                 let uu___6 =
                                   let uu___7 =
                                     let uu___8 =
                                       FStarC_Tactics_Types.goal_env g in
                                     let uu___9 =
                                       FStarC_Tactics_Types.goal_opts g in
                                     (uu___8, gt', uu___9) in
                                   uu___7 :: gs1 in
                                 ((n + Prims.int_one), uu___6)))) s gs in
                  let uu___4 = s1 in
                  match uu___4 with
                  | (uu___5, gs1) ->
                      let gs2 = FStarC_Compiler_List.rev gs1 in
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = FStarC_Options.peek () in
                          (env, t', uu___8) in
                        uu___7 :: gs2 in
                      (did_anything, uu___6)))))
let rec (traverse_for_spinoff :
  pol ->
    (FStarC_Pprint.document Prims.list * FStarC_Compiler_Range_Type.range)
      FStar_Pervasives_Native.option ->
      FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> tres)
  =
  fun pol1 ->
    fun label_ctx ->
      fun e ->
        fun t ->
          let debug_any = FStarC_Compiler_Debug.any () in
          let traverse1 pol2 e1 t1 =
            traverse_for_spinoff pol2 label_ctx e1 t1 in
          let traverse_ctx pol2 ctx e1 t1 =
            let print_lc uu___ =
              match uu___ with
              | (msg, rng) ->
                  let uu___1 =
                    FStarC_Compiler_Range_Ops.string_of_def_range rng in
                  let uu___2 =
                    FStarC_Compiler_Range_Ops.string_of_use_range rng in
                  let uu___3 = FStarC_Errors_Msg.rendermsg msg in
                  FStarC_Compiler_Util.format3 "(%s,%s) : %s" uu___1 uu___2
                    uu___3 in
            (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_SpinoffAll in
             if uu___1
             then
               let uu___2 =
                 match label_ctx with
                 | FStar_Pervasives_Native.None -> "None"
                 | FStar_Pervasives_Native.Some lc -> print_lc lc in
               let uu___3 = print_lc ctx in
               FStarC_Compiler_Util.print2
                 "Changing label context from %s to %s" uu___2 uu___3
             else ());
            traverse_for_spinoff pol2 (FStar_Pervasives_Native.Some ctx) e1
              t1 in
          let should_descend t1 =
            let uu___ = FStarC_Syntax_Util.head_and_args t1 in
            match uu___ with
            | (hd, args) ->
                let res =
                  let uu___1 =
                    let uu___2 = FStarC_Syntax_Util.un_uinst hd in
                    uu___2.FStarC_Syntax_Syntax.n in
                  match uu___1 with
                  | FStarC_Syntax_Syntax.Tm_fvar fv ->
                      ((((FStarC_Syntax_Syntax.fv_eq_lid fv
                            FStarC_Parser_Const.and_lid)
                           ||
                           (FStarC_Syntax_Syntax.fv_eq_lid fv
                              FStarC_Parser_Const.imp_lid))
                          ||
                          (FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Parser_Const.forall_lid))
                         ||
                         (FStarC_Syntax_Syntax.fv_eq_lid fv
                            FStarC_Parser_Const.auto_squash_lid))
                        ||
                        (FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Parser_Const.squash_lid)
                  | FStarC_Syntax_Syntax.Tm_meta uu___2 -> true
                  | FStarC_Syntax_Syntax.Tm_ascribed uu___2 -> true
                  | FStarC_Syntax_Syntax.Tm_abs uu___2 -> true
                  | uu___2 -> false in
                res in
          let maybe_spinoff pol2 label_ctx1 e1 t1 =
            let label_goal uu___ =
              match uu___ with
              | (env, t2) ->
                  let t3 =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = FStarC_Syntax_Subst.compress t2 in
                        uu___3.FStarC_Syntax_Syntax.n in
                      (uu___2, label_ctx1) in
                    match uu___1 with
                    | (FStarC_Syntax_Syntax.Tm_meta
                       { FStarC_Syntax_Syntax.tm2 = uu___2;
                         FStarC_Syntax_Syntax.meta =
                           FStarC_Syntax_Syntax.Meta_labeled uu___3;_},
                       uu___4) -> t2
                    | (uu___2, FStar_Pervasives_Native.Some (msg, r)) ->
                        FStarC_TypeChecker_Util.label msg r t2
                    | uu___2 -> t2 in
                  let t4 =
                    let uu___1 = FStarC_Syntax_Util.is_sub_singleton t3 in
                    if uu___1
                    then t3
                    else
                      FStarC_Syntax_Util.mk_auto_squash
                        FStarC_Syntax_Syntax.U_zero t3 in
                  let uu___1 = FStarC_Tactics_Types.goal_of_goal_ty env t4 in
                  FStar_Pervasives_Native.fst uu___1 in
            let spinoff t2 =
              match pol2 with
              | StrictlyPositive ->
                  ((let uu___1 =
                      FStarC_Compiler_Effect.op_Bang dbg_SpinoffAll in
                    if uu___1
                    then
                      let uu___2 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term t2 in
                      FStarC_Compiler_Util.print1 "Spinning off %s\n" uu___2
                    else ());
                   (let uu___1 =
                      let uu___2 =
                        let uu___3 = label_goal (e1, t2) in [uu___3] in
                      (FStarC_Syntax_Util.t_true, uu___2) in
                    Simplified uu___1))
              | uu___ -> Unchanged t2 in
            let t2 = FStarC_Syntax_Subst.compress t1 in
            let uu___ =
              let uu___1 = should_descend t2 in Prims.op_Negation uu___1 in
            if uu___ then spinoff t2 else Unchanged t2 in
          let rewrite_boolean_conjunction t1 =
            let uu___ = FStarC_Syntax_Util.head_and_args t1 in
            match uu___ with
            | (hd, args) ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                    uu___3.FStarC_Syntax_Syntax.n in
                  (uu___2, args) in
                (match uu___1 with
                 | (FStarC_Syntax_Syntax.Tm_fvar fv, (t2, uu___2)::[]) when
                     FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Parser_Const.b2t_lid
                     ->
                     let uu___3 = FStarC_Syntax_Util.head_and_args t2 in
                     (match uu___3 with
                      | (hd1, args1) ->
                          let uu___4 =
                            let uu___5 =
                              let uu___6 = FStarC_Syntax_Util.un_uinst hd1 in
                              uu___6.FStarC_Syntax_Syntax.n in
                            (uu___5, args1) in
                          (match uu___4 with
                           | (FStarC_Syntax_Syntax.Tm_fvar fv1,
                              (t0, uu___5)::(t11, uu___6)::[]) when
                               FStarC_Syntax_Syntax.fv_eq_lid fv1
                                 FStarC_Parser_Const.op_And
                               ->
                               let t3 =
                                 let uu___7 = FStarC_Syntax_Util.b2t t0 in
                                 let uu___8 = FStarC_Syntax_Util.b2t t11 in
                                 FStarC_Syntax_Util.mk_conj uu___7 uu___8 in
                               FStar_Pervasives_Native.Some t3
                           | uu___5 -> FStar_Pervasives_Native.None))
                 | uu___2 -> FStar_Pervasives_Native.None) in
          let try_rewrite_match env t1 =
            let rec pat_as_exp env1 p =
              let uu___ =
                FStarC_TypeChecker_PatternUtils.raw_pat_as_exp env1 p in
              match uu___ with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (e1, uu___1) ->
                  let uu___2 = FStarC_TypeChecker_Env.clear_expected_typ env1 in
                  (match uu___2 with
                   | (env2, uu___3) ->
                       let uu___4 =
                         FStarC_TypeChecker_TcTerm.tc_trivial_guard
                           {
                             FStarC_TypeChecker_Env.solver =
                               (env2.FStarC_TypeChecker_Env.solver);
                             FStarC_TypeChecker_Env.range =
                               (env2.FStarC_TypeChecker_Env.range);
                             FStarC_TypeChecker_Env.curmodule =
                               (env2.FStarC_TypeChecker_Env.curmodule);
                             FStarC_TypeChecker_Env.gamma =
                               (env2.FStarC_TypeChecker_Env.gamma);
                             FStarC_TypeChecker_Env.gamma_sig =
                               (env2.FStarC_TypeChecker_Env.gamma_sig);
                             FStarC_TypeChecker_Env.gamma_cache =
                               (env2.FStarC_TypeChecker_Env.gamma_cache);
                             FStarC_TypeChecker_Env.modules =
                               (env2.FStarC_TypeChecker_Env.modules);
                             FStarC_TypeChecker_Env.expected_typ =
                               (env2.FStarC_TypeChecker_Env.expected_typ);
                             FStarC_TypeChecker_Env.sigtab =
                               (env2.FStarC_TypeChecker_Env.sigtab);
                             FStarC_TypeChecker_Env.attrtab =
                               (env2.FStarC_TypeChecker_Env.attrtab);
                             FStarC_TypeChecker_Env.instantiate_imp =
                               (env2.FStarC_TypeChecker_Env.instantiate_imp);
                             FStarC_TypeChecker_Env.effects =
                               (env2.FStarC_TypeChecker_Env.effects);
                             FStarC_TypeChecker_Env.generalize =
                               (env2.FStarC_TypeChecker_Env.generalize);
                             FStarC_TypeChecker_Env.letrecs =
                               (env2.FStarC_TypeChecker_Env.letrecs);
                             FStarC_TypeChecker_Env.top_level =
                               (env2.FStarC_TypeChecker_Env.top_level);
                             FStarC_TypeChecker_Env.check_uvars =
                               (env2.FStarC_TypeChecker_Env.check_uvars);
                             FStarC_TypeChecker_Env.use_eq_strict =
                               (env2.FStarC_TypeChecker_Env.use_eq_strict);
                             FStarC_TypeChecker_Env.is_iface =
                               (env2.FStarC_TypeChecker_Env.is_iface);
                             FStarC_TypeChecker_Env.admit = true;
                             FStarC_TypeChecker_Env.lax_universes =
                               (env2.FStarC_TypeChecker_Env.lax_universes);
                             FStarC_TypeChecker_Env.phase1 =
                               (env2.FStarC_TypeChecker_Env.phase1);
                             FStarC_TypeChecker_Env.failhard =
                               (env2.FStarC_TypeChecker_Env.failhard);
                             FStarC_TypeChecker_Env.flychecking =
                               (env2.FStarC_TypeChecker_Env.flychecking);
                             FStarC_TypeChecker_Env.uvar_subtyping =
                               (env2.FStarC_TypeChecker_Env.uvar_subtyping);
                             FStarC_TypeChecker_Env.intactics =
                               (env2.FStarC_TypeChecker_Env.intactics);
                             FStarC_TypeChecker_Env.nocoerce =
                               (env2.FStarC_TypeChecker_Env.nocoerce);
                             FStarC_TypeChecker_Env.tc_term =
                               (env2.FStarC_TypeChecker_Env.tc_term);
                             FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                               (env2.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                             FStarC_TypeChecker_Env.universe_of =
                               (env2.FStarC_TypeChecker_Env.universe_of);
                             FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                               =
                               (env2.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                             FStarC_TypeChecker_Env.teq_nosmt_force =
                               (env2.FStarC_TypeChecker_Env.teq_nosmt_force);
                             FStarC_TypeChecker_Env.subtype_nosmt_force =
                               (env2.FStarC_TypeChecker_Env.subtype_nosmt_force);
                             FStarC_TypeChecker_Env.qtbl_name_and_index =
                               (env2.FStarC_TypeChecker_Env.qtbl_name_and_index);
                             FStarC_TypeChecker_Env.normalized_eff_names =
                               (env2.FStarC_TypeChecker_Env.normalized_eff_names);
                             FStarC_TypeChecker_Env.fv_delta_depths =
                               (env2.FStarC_TypeChecker_Env.fv_delta_depths);
                             FStarC_TypeChecker_Env.proof_ns =
                               (env2.FStarC_TypeChecker_Env.proof_ns);
                             FStarC_TypeChecker_Env.synth_hook =
                               (env2.FStarC_TypeChecker_Env.synth_hook);
                             FStarC_TypeChecker_Env.try_solve_implicits_hook
                               =
                               (env2.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                             FStarC_TypeChecker_Env.splice =
                               (env2.FStarC_TypeChecker_Env.splice);
                             FStarC_TypeChecker_Env.mpreprocess =
                               (env2.FStarC_TypeChecker_Env.mpreprocess);
                             FStarC_TypeChecker_Env.postprocess =
                               (env2.FStarC_TypeChecker_Env.postprocess);
                             FStarC_TypeChecker_Env.identifier_info =
                               (env2.FStarC_TypeChecker_Env.identifier_info);
                             FStarC_TypeChecker_Env.tc_hooks =
                               (env2.FStarC_TypeChecker_Env.tc_hooks);
                             FStarC_TypeChecker_Env.dsenv =
                               (env2.FStarC_TypeChecker_Env.dsenv);
                             FStarC_TypeChecker_Env.nbe =
                               (env2.FStarC_TypeChecker_Env.nbe);
                             FStarC_TypeChecker_Env.strict_args_tab =
                               (env2.FStarC_TypeChecker_Env.strict_args_tab);
                             FStarC_TypeChecker_Env.erasable_types_tab =
                               (env2.FStarC_TypeChecker_Env.erasable_types_tab);
                             FStarC_TypeChecker_Env.enable_defer_to_tac =
                               (env2.FStarC_TypeChecker_Env.enable_defer_to_tac);
                             FStarC_TypeChecker_Env.unif_allow_ref_guards =
                               (env2.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                             FStarC_TypeChecker_Env.erase_erasable_args =
                               (env2.FStarC_TypeChecker_Env.erase_erasable_args);
                             FStarC_TypeChecker_Env.core_check =
                               (env2.FStarC_TypeChecker_Env.core_check);
                             FStarC_TypeChecker_Env.missing_decl =
                               (env2.FStarC_TypeChecker_Env.missing_decl)
                           } e1 in
                       (match uu___4 with
                        | (e2, lc) ->
                            let u =
                              FStarC_TypeChecker_TcTerm.universe_of env2
                                lc.FStarC_TypeChecker_Common.res_typ in
                            FStar_Pervasives_Native.Some
                              (e2, (lc.FStarC_TypeChecker_Common.res_typ), u))) in
            let bv_universes env1 bvs =
              FStarC_Compiler_List.map
                (fun x ->
                   let uu___ =
                     FStarC_TypeChecker_TcTerm.universe_of env1
                       x.FStarC_Syntax_Syntax.sort in
                   (x, uu___)) bvs in
            let mk_forall_l bv_univs term =
              FStarC_Compiler_List.fold_right
                (fun uu___ ->
                   fun out ->
                     match uu___ with
                     | (x, u) -> FStarC_Syntax_Util.mk_forall u x out)
                bv_univs term in
            let mk_exists_l bv_univs term =
              FStarC_Compiler_List.fold_right
                (fun uu___ ->
                   fun out ->
                     match uu___ with
                     | (x, u) -> FStarC_Syntax_Util.mk_exists u x out)
                bv_univs term in
            if pol1 <> StrictlyPositive
            then FStar_Pervasives_Native.None
            else
              (let uu___1 =
                 let uu___2 = FStarC_Syntax_Subst.compress t1 in
                 uu___2.FStarC_Syntax_Syntax.n in
               match uu___1 with
               | FStarC_Syntax_Syntax.Tm_match
                   { FStarC_Syntax_Syntax.scrutinee = sc;
                     FStarC_Syntax_Syntax.ret_opt = asc_opt;
                     FStarC_Syntax_Syntax.brs = brs;
                     FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
                   ->
                   let rec rewrite_branches path_condition branches =
                     match branches with
                     | [] ->
                         let uu___2 =
                           FStarC_Syntax_Util.mk_imp path_condition
                             FStarC_Syntax_Util.t_false in
                         FStar_Pervasives.Inr uu___2
                     | br::branches1 ->
                         let uu___2 = FStarC_Syntax_Subst.open_branch br in
                         (match uu___2 with
                          | (pat, w, body) ->
                              (match w with
                               | FStar_Pervasives_Native.Some uu___3 ->
                                   FStar_Pervasives.Inl "when clause"
                               | uu___3 ->
                                   let bvs = FStarC_Syntax_Syntax.pat_bvs pat in
                                   let env1 =
                                     FStarC_TypeChecker_Env.push_bvs env bvs in
                                   let bvs_univs = bv_universes env1 bvs in
                                   let uu___4 = pat_as_exp env1 pat in
                                   (match uu___4 with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Pervasives.Inl
                                          "Ill-typed pattern"
                                    | FStar_Pervasives_Native.Some
                                        (p_e, t2, u) ->
                                        let eqn =
                                          FStarC_Syntax_Util.mk_eq2 u t2 sc
                                            p_e in
                                        let branch_goal =
                                          let uu___5 =
                                            FStarC_Syntax_Util.mk_imp eqn
                                              body in
                                          mk_forall_l bvs_univs uu___5 in
                                        let branch_goal1 =
                                          FStarC_Syntax_Util.mk_imp
                                            path_condition branch_goal in
                                        let next_path_condition =
                                          let uu___5 =
                                            let uu___6 =
                                              mk_exists_l bvs_univs eqn in
                                            FStarC_Syntax_Util.mk_neg uu___6 in
                                          FStarC_Syntax_Util.mk_conj
                                            path_condition uu___5 in
                                        let uu___5 =
                                          rewrite_branches
                                            next_path_condition branches1 in
                                        (match uu___5 with
                                         | FStar_Pervasives.Inl msg ->
                                             FStar_Pervasives.Inl msg
                                         | FStar_Pervasives.Inr rest ->
                                             let uu___6 =
                                               FStarC_Syntax_Util.mk_conj
                                                 branch_goal1 rest in
                                             FStar_Pervasives.Inr uu___6)))) in
                   let res = rewrite_branches FStarC_Syntax_Util.t_true brs in
                   (match res with
                    | FStar_Pervasives.Inl msg ->
                        (if debug_any
                         then
                           (let uu___3 = FStarC_TypeChecker_Env.get_range env in
                            let uu___4 =
                              let uu___5 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term t1 in
                              FStarC_Compiler_Util.format2
                                "Failed to split match term because %s (%s)"
                                msg uu___5 in
                            FStarC_Errors.diag
                              FStarC_Class_HasRange.hasRange_range uu___3 ()
                              (Obj.magic
                                 FStarC_Errors_Msg.is_error_message_string)
                              (Obj.magic uu___4))
                         else ();
                         FStar_Pervasives_Native.None)
                    | FStar_Pervasives.Inr res1 ->
                        (if debug_any
                         then
                           (let uu___3 = FStarC_TypeChecker_Env.get_range env in
                            let uu___4 =
                              let uu___5 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term t1 in
                              let uu___6 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term res1 in
                              FStarC_Compiler_Util.format2
                                "Rewrote match term\n%s\ninto %s\n" uu___5
                                uu___6 in
                            FStarC_Errors.diag
                              FStarC_Class_HasRange.hasRange_range uu___3 ()
                              (Obj.magic
                                 FStarC_Errors_Msg.is_error_message_string)
                              (Obj.magic uu___4))
                         else ();
                         FStar_Pervasives_Native.Some res1))
               | uu___2 -> FStar_Pervasives_Native.None) in
          let maybe_rewrite_term t1 =
            if pol1 <> StrictlyPositive
            then FStar_Pervasives_Native.None
            else
              (let uu___1 = rewrite_boolean_conjunction t1 in
               match uu___1 with
               | FStar_Pervasives_Native.Some t2 ->
                   FStar_Pervasives_Native.Some t2
               | FStar_Pervasives_Native.None -> try_rewrite_match e t1) in
          let uu___ = maybe_rewrite_term t in
          match uu___ with
          | FStar_Pervasives_Native.Some t1 -> traverse1 pol1 e t1
          | uu___1 ->
              let r =
                let t1 = FStarC_Syntax_Subst.compress t in
                let uu___2 =
                  let uu___3 = should_descend t1 in Prims.op_Negation uu___3 in
                if uu___2
                then tpure t1.FStarC_Syntax_Syntax.n
                else
                  (match t1.FStarC_Syntax_Syntax.n with
                   | FStarC_Syntax_Syntax.Tm_uinst (t2, us) ->
                       let tr = traverse1 pol1 e t2 in
                       let uu___4 =
                         comb1
                           (fun t' -> FStarC_Syntax_Syntax.Tm_uinst (t', us)) in
                       uu___4 tr
                   | FStarC_Syntax_Syntax.Tm_meta
                       { FStarC_Syntax_Syntax.tm2 = t2;
                         FStarC_Syntax_Syntax.meta =
                           FStarC_Syntax_Syntax.Meta_labeled
                           (msg, r1, uu___4);_}
                       ->
                       let tr = traverse_ctx pol1 (msg, r1) e t2 in
                       let uu___5 =
                         comb1
                           (fun t' ->
                              FStarC_Syntax_Syntax.Tm_meta
                                {
                                  FStarC_Syntax_Syntax.tm2 = t';
                                  FStarC_Syntax_Syntax.meta =
                                    (FStarC_Syntax_Syntax.Meta_labeled
                                       (msg, r1, false))
                                }) in
                       uu___5 tr
                   | FStarC_Syntax_Syntax.Tm_meta
                       { FStarC_Syntax_Syntax.tm2 = t2;
                         FStarC_Syntax_Syntax.meta = m;_}
                       ->
                       let tr = traverse1 pol1 e t2 in
                       let uu___4 =
                         comb1
                           (fun t' ->
                              FStarC_Syntax_Syntax.Tm_meta
                                {
                                  FStarC_Syntax_Syntax.tm2 = t';
                                  FStarC_Syntax_Syntax.meta = m
                                }) in
                       uu___4 tr
                   | FStarC_Syntax_Syntax.Tm_ascribed
                       { FStarC_Syntax_Syntax.tm = t2;
                         FStarC_Syntax_Syntax.asc = asc;
                         FStarC_Syntax_Syntax.eff_opt = ef;_}
                       ->
                       let uu___4 = traverse1 pol1 e t2 in
                       let uu___5 =
                         comb1
                           (fun t3 ->
                              FStarC_Syntax_Syntax.Tm_ascribed
                                {
                                  FStarC_Syntax_Syntax.tm = t3;
                                  FStarC_Syntax_Syntax.asc = asc;
                                  FStarC_Syntax_Syntax.eff_opt = ef
                                }) in
                       uu___5 uu___4
                   | FStarC_Syntax_Syntax.Tm_app
                       {
                         FStarC_Syntax_Syntax.hd =
                           {
                             FStarC_Syntax_Syntax.n =
                               FStarC_Syntax_Syntax.Tm_fvar fv;
                             FStarC_Syntax_Syntax.pos = uu___4;
                             FStarC_Syntax_Syntax.vars = uu___5;
                             FStarC_Syntax_Syntax.hash_code = uu___6;_};
                         FStarC_Syntax_Syntax.args =
                           (p, uu___7)::(q, uu___8)::[];_}
                       when
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.imp_lid
                       ->
                       let x =
                         FStarC_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None p in
                       let r1 = traverse1 (flip pol1) e p in
                       let r2 =
                         let uu___9 = FStarC_TypeChecker_Env.push_bv e x in
                         traverse1 pol1 uu___9 q in
                       comb2
                         (fun l ->
                            fun r3 ->
                              let uu___9 = FStarC_Syntax_Util.mk_imp l r3 in
                              uu___9.FStarC_Syntax_Syntax.n) r1 r2
                   | FStarC_Syntax_Syntax.Tm_app
                       { FStarC_Syntax_Syntax.hd = hd;
                         FStarC_Syntax_Syntax.args = args;_}
                       ->
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = FStarC_Syntax_Util.un_uinst hd in
                           uu___6.FStarC_Syntax_Syntax.n in
                         (uu___5, args) in
                       (match uu___4 with
                        | (FStarC_Syntax_Syntax.Tm_fvar fv,
                           (t2, FStar_Pervasives_Native.Some aq0)::(body, aq)::[])
                            when
                            ((FStarC_Syntax_Syntax.fv_eq_lid fv
                                FStarC_Parser_Const.forall_lid)
                               ||
                               (FStarC_Syntax_Syntax.fv_eq_lid fv
                                  FStarC_Parser_Const.exists_lid))
                              && aq0.FStarC_Syntax_Syntax.aqual_implicit
                            ->
                            let r0 = traverse1 pol1 e hd in
                            let rt = traverse1 (flip pol1) e t2 in
                            let rbody = traverse1 pol1 e body in
                            let rargs =
                              comb2
                                (fun t3 ->
                                   fun body1 ->
                                     [(t3,
                                        (FStar_Pervasives_Native.Some aq0));
                                     (body1, aq)]) rt rbody in
                            comb2
                              (fun hd1 ->
                                 fun args1 ->
                                   FStarC_Syntax_Syntax.Tm_app
                                     {
                                       FStarC_Syntax_Syntax.hd = hd1;
                                       FStarC_Syntax_Syntax.args = args1
                                     }) r0 rargs
                        | uu___5 ->
                            let r0 = traverse1 pol1 e hd in
                            let r1 =
                              FStarC_Compiler_List.fold_right
                                (fun uu___6 ->
                                   fun r2 ->
                                     match uu___6 with
                                     | (a, q) ->
                                         let r' = traverse1 pol1 e a in
                                         comb2
                                           (fun a1 ->
                                              fun args1 -> (a1, q) :: args1)
                                           r' r2) args (tpure []) in
                            let simplified =
                              (uu___is_Simplified r0) ||
                                (uu___is_Simplified r1) in
                            comb2
                              (fun hd1 ->
                                 fun args1 ->
                                   let uu___6 =
                                     let uu___7 =
                                       let uu___8 =
                                         FStarC_Syntax_Util.un_uinst hd1 in
                                       uu___8.FStarC_Syntax_Syntax.n in
                                     (uu___7, args1) in
                                   match uu___6 with
                                   | (FStarC_Syntax_Syntax.Tm_fvar fv,
                                      (t2, uu___7)::[]) when
                                       (simplified &&
                                          (FStarC_Syntax_Syntax.fv_eq_lid fv
                                             FStarC_Parser_Const.squash_lid))
                                         &&
                                         (let uu___8 =
                                            FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                              e t2 FStarC_Syntax_Util.t_true in
                                          uu___8 =
                                            FStarC_TypeChecker_TermEqAndSimplify.Equal)
                                       ->
                                       ((let uu___9 =
                                           FStarC_Compiler_Effect.op_Bang
                                             dbg_SpinoffAll in
                                         if uu___9
                                         then
                                           FStarC_Compiler_Util.print_string
                                             "Simplified squash True to True"
                                         else ());
                                        FStarC_Syntax_Util.t_true.FStarC_Syntax_Syntax.n)
                                   | uu___7 ->
                                       let t' =
                                         FStarC_Syntax_Syntax.Tm_app
                                           {
                                             FStarC_Syntax_Syntax.hd = hd1;
                                             FStarC_Syntax_Syntax.args =
                                               args1
                                           } in
                                       t') r0 r1)
                   | FStarC_Syntax_Syntax.Tm_abs
                       { FStarC_Syntax_Syntax.bs = bs;
                         FStarC_Syntax_Syntax.body = t2;
                         FStarC_Syntax_Syntax.rc_opt = k;_}
                       ->
                       let uu___4 = FStarC_Syntax_Subst.open_term bs t2 in
                       (match uu___4 with
                        | (bs1, topen) ->
                            let e' =
                              FStarC_TypeChecker_Env.push_binders e bs1 in
                            let r0 =
                              FStarC_Compiler_List.map
                                (fun b ->
                                   let r1 =
                                     traverse1 (flip pol1) e
                                       (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                   let uu___5 =
                                     comb1
                                       (fun s' ->
                                          {
                                            FStarC_Syntax_Syntax.binder_bv =
                                              (let uu___6 =
                                                 b.FStarC_Syntax_Syntax.binder_bv in
                                               {
                                                 FStarC_Syntax_Syntax.ppname
                                                   =
                                                   (uu___6.FStarC_Syntax_Syntax.ppname);
                                                 FStarC_Syntax_Syntax.index =
                                                   (uu___6.FStarC_Syntax_Syntax.index);
                                                 FStarC_Syntax_Syntax.sort =
                                                   s'
                                               });
                                            FStarC_Syntax_Syntax.binder_qual
                                              =
                                              (b.FStarC_Syntax_Syntax.binder_qual);
                                            FStarC_Syntax_Syntax.binder_positivity
                                              =
                                              (b.FStarC_Syntax_Syntax.binder_positivity);
                                            FStarC_Syntax_Syntax.binder_attrs
                                              =
                                              (b.FStarC_Syntax_Syntax.binder_attrs)
                                          }) in
                                   uu___5 r1) bs1 in
                            let rbs = comb_list r0 in
                            let rt = traverse1 pol1 e' topen in
                            comb2
                              (fun bs2 ->
                                 fun t3 ->
                                   let uu___5 =
                                     FStarC_Syntax_Util.abs bs2 t3 k in
                                   uu___5.FStarC_Syntax_Syntax.n) rbs rt)
                   | x -> tpure x) in
              (match r with
               | Unchanged tn' ->
                   maybe_spinoff pol1 label_ctx e
                     {
                       FStarC_Syntax_Syntax.n = tn';
                       FStarC_Syntax_Syntax.pos =
                         (t.FStarC_Syntax_Syntax.pos);
                       FStarC_Syntax_Syntax.vars =
                         (t.FStarC_Syntax_Syntax.vars);
                       FStarC_Syntax_Syntax.hash_code =
                         (t.FStarC_Syntax_Syntax.hash_code)
                     }
               | Simplified (tn', gs) ->
                   let uu___2 =
                     maybe_spinoff pol1 label_ctx e
                       {
                         FStarC_Syntax_Syntax.n = tn';
                         FStarC_Syntax_Syntax.pos =
                           (t.FStarC_Syntax_Syntax.pos);
                         FStarC_Syntax_Syntax.vars =
                           (t.FStarC_Syntax_Syntax.vars);
                         FStarC_Syntax_Syntax.hash_code =
                           (t.FStarC_Syntax_Syntax.hash_code)
                       } in
                   emit gs uu___2
               | Dual (tn, tp, gs) ->
                   let rp =
                     maybe_spinoff pol1 label_ctx e
                       {
                         FStarC_Syntax_Syntax.n = tp;
                         FStarC_Syntax_Syntax.pos =
                           (t.FStarC_Syntax_Syntax.pos);
                         FStarC_Syntax_Syntax.vars =
                           (t.FStarC_Syntax_Syntax.vars);
                         FStarC_Syntax_Syntax.hash_code =
                           (t.FStarC_Syntax_Syntax.hash_code)
                       } in
                   let uu___2 = explode rp in
                   (match uu___2 with
                    | (uu___3, p', gs') ->
                        Dual
                          ({
                             FStarC_Syntax_Syntax.n = tn;
                             FStarC_Syntax_Syntax.pos =
                               (t.FStarC_Syntax_Syntax.pos);
                             FStarC_Syntax_Syntax.vars =
                               (t.FStarC_Syntax_Syntax.vars);
                             FStarC_Syntax_Syntax.hash_code =
                               (t.FStarC_Syntax_Syntax.hash_code)
                           }, p', (FStarC_Compiler_List.op_At gs gs'))))
let (pol_to_string : pol -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | StrictlyPositive -> "StrictlyPositive"
    | Pos -> "Positive"
    | Neg -> "Negative"
    | Both -> "Both"
let (spinoff_strictly_positive_goals :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_TypeChecker_Env.env * FStarC_Syntax_Syntax.term) Prims.list)
  =
  fun env ->
    fun goal ->
      (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_SpinoffAll in
       if uu___1
       then
         let uu___2 =
           FStarC_Class_Show.show FStarC_Syntax_Print.showable_term goal in
         FStarC_Compiler_Util.print1 "spinoff_all called with %s\n" uu___2
       else ());
      FStarC_Errors.with_ctx "While spinning off all goals"
        (fun uu___1 ->
           let initial = (Prims.int_one, []) in
           let uu___2 =
             let uu___3 =
               traverse_for_spinoff StrictlyPositive
                 FStar_Pervasives_Native.None env goal in
             match uu___3 with
             | Unchanged t' -> (t', [])
             | Simplified (t', gs) -> (t', gs)
             | uu___4 ->
                 failwith "preprocess: impossible, traverse returned a Dual" in
           match uu___2 with
           | (t', gs) ->
               let t'1 =
                 FStarC_TypeChecker_Normalize.normalize
                   [FStarC_TypeChecker_Env.Eager_unfolding;
                   FStarC_TypeChecker_Env.Simplify;
                   FStarC_TypeChecker_Env.Primops] env t' in
               let main_goal =
                 let t = FStarC_TypeChecker_Common.check_trivial t'1 in
                 match t with
                 | FStarC_TypeChecker_Common.Trivial -> []
                 | FStarC_TypeChecker_Common.NonTrivial t1 ->
                     ((let uu___4 =
                         FStarC_Compiler_Effect.op_Bang dbg_SpinoffAll in
                       if uu___4
                       then
                         let msg =
                           let uu___5 =
                             let uu___6 =
                               FStarC_TypeChecker_Env.all_binders env in
                             FStarC_Class_Show.show
                               (FStarC_Class_Show.show_list
                                  FStarC_Syntax_Print.showable_binder) uu___6 in
                           let uu___6 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term t1 in
                           FStarC_Compiler_Util.format2
                             "Main goal simplified to: %s |- %s\n" uu___5
                             uu___6 in
                         let uu___5 = FStarC_TypeChecker_Env.get_range env in
                         let uu___6 =
                           FStarC_Compiler_Util.format1
                             "Verification condition was to be split into several atomic sub-goals, but this query had some sub-goals that couldn't be split---the error report, if any, may be inaccurate.\n%s\n"
                             msg in
                         FStarC_Errors.diag
                           FStarC_Class_HasRange.hasRange_range uu___5 ()
                           (Obj.magic
                              FStarC_Errors_Msg.is_error_message_string)
                           (Obj.magic uu___6)
                       else ());
                      [(env, t1)]) in
               let s = initial in
               let s1 =
                 FStarC_Compiler_List.fold_left
                   (fun uu___3 ->
                      fun g ->
                        match uu___3 with
                        | (n, gs1) ->
                            let phi = FStarC_Tactics_Types.goal_type g in
                            let uu___4 =
                              let uu___5 =
                                let uu___6 = FStarC_Tactics_Types.goal_env g in
                                (uu___6, phi) in
                              uu___5 :: gs1 in
                            ((n + Prims.int_one), uu___4)) s gs in
               let uu___3 = s1 in
               (match uu___3 with
                | (uu___4, gs1) ->
                    let gs2 = FStarC_Compiler_List.rev gs1 in
                    let gs3 =
                      FStarC_Compiler_List.filter_map
                        (fun uu___5 ->
                           match uu___5 with
                           | (env1, t) ->
                               let t1 =
                                 FStarC_TypeChecker_Normalize.normalize
                                   [FStarC_TypeChecker_Env.Eager_unfolding;
                                   FStarC_TypeChecker_Env.Simplify;
                                   FStarC_TypeChecker_Env.Primops] env1 t in
                               let uu___6 =
                                 FStarC_TypeChecker_Common.check_trivial t1 in
                               (match uu___6 with
                                | FStarC_TypeChecker_Common.Trivial ->
                                    FStar_Pervasives_Native.None
                                | FStarC_TypeChecker_Common.NonTrivial t2 ->
                                    ((let uu___8 =
                                        FStarC_Compiler_Effect.op_Bang
                                          dbg_SpinoffAll in
                                      if uu___8
                                      then
                                        let uu___9 =
                                          FStarC_Class_Show.show
                                            FStarC_Syntax_Print.showable_term
                                            t2 in
                                        FStarC_Compiler_Util.print1
                                          "Got goal: %s\n" uu___9
                                      else ());
                                     FStar_Pervasives_Native.Some (env1, t2))))
                        gs2 in
                    ((let uu___6 = FStarC_TypeChecker_Env.get_range env in
                      let uu___7 =
                        let uu___8 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_nat
                            (FStarC_Compiler_List.length gs3) in
                        FStarC_Compiler_Util.format1
                          "Split query into %s sub-goals" uu___8 in
                      FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
                        uu___6 ()
                        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                        (Obj.magic uu___7));
                     FStarC_Compiler_List.op_At main_goal gs3)))
let (synthesize :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun typ ->
      fun tau ->
        FStarC_Errors.with_ctx "While synthesizing term with a tactic"
          (fun uu___ ->
             if env.FStarC_TypeChecker_Env.flychecking
             then
               let uu___1 =
                 FStarC_TypeChecker_Util.fvar_env env
                   FStarC_Parser_Const.magic_lid in
               let uu___2 =
                 let uu___3 =
                   FStarC_Syntax_Syntax.as_arg FStarC_Syntax_Util.exp_unit in
                 [uu___3] in
               FStarC_Syntax_Syntax.mk_Tm_app uu___1 uu___2
                 typ.FStarC_Syntax_Syntax.pos
             else
               (let uu___2 =
                  run_tactic_on_typ tau.FStarC_Syntax_Syntax.pos
                    typ.FStarC_Syntax_Syntax.pos tau env typ in
                match uu___2 with
                | (gs, w) ->
                    (FStarC_Compiler_List.iter
                       (fun g ->
                          let uu___4 =
                            let uu___5 = FStarC_Tactics_Types.goal_env g in
                            let uu___6 = FStarC_Tactics_Types.goal_type g in
                            getprop uu___5 uu___6 in
                          match uu___4 with
                          | FStar_Pervasives_Native.Some vc ->
                              ((let uu___6 =
                                  FStarC_Compiler_Effect.op_Bang dbg_Tac in
                                if uu___6
                                then
                                  let uu___7 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_term vc in
                                  FStarC_Compiler_Util.print1
                                    "Synthesis left a goal: %s\n" uu___7
                                else ());
                               (let guard =
                                  FStarC_TypeChecker_Env.guard_of_guard_formula
                                    (FStarC_TypeChecker_Common.NonTrivial vc) in
                                let uu___6 = FStarC_Tactics_Types.goal_env g in
                                FStarC_TypeChecker_Rel.force_trivial_guard
                                  uu___6 guard))
                          | FStar_Pervasives_Native.None ->
                              FStarC_Errors.raise_error
                                (FStarC_Syntax_Syntax.has_range_syntax ())
                                typ
                                FStarC_Errors_Codes.Fatal_OpenGoalsInSynthesis
                                ()
                                (Obj.magic
                                   FStarC_Errors_Msg.is_error_message_string)
                                (Obj.magic "synthesis left open goals")) gs;
                     w)))
let (solve_implicits :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_TypeChecker_Env.implicits -> unit)
  =
  fun env ->
    fun tau ->
      fun imps ->
        FStarC_Errors.with_ctx "While solving implicits with a tactic"
          (fun uu___ ->
             if env.FStarC_TypeChecker_Env.flychecking
             then ()
             else
               (let gs =
                  let uu___2 = FStarC_TypeChecker_Env.get_range env in
                  run_tactic_on_all_implicits tau.FStarC_Syntax_Syntax.pos
                    uu___2 tau env imps in
                (let uu___3 =
                   FStarC_Options.profile_enabled
                     FStar_Pervasives_Native.None "FStarC.TypeChecker" in
                 if uu___3
                 then
                   let uu___4 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                       (FStarC_Compiler_List.length gs) in
                   FStarC_Compiler_Util.print1
                     "solve_implicits produced %s goals\n" uu___4
                 else ());
                FStarC_Options.with_saved_options
                  (fun uu___3 ->
                     let uu___4 = FStarC_Options.set_options "--no_tactics" in
                     FStarC_Compiler_List.iter
                       (fun g ->
                          (let uu___6 = FStarC_Tactics_Types.goal_opts g in
                           FStarC_Options.set uu___6);
                          (let uu___6 =
                             let uu___7 = FStarC_Tactics_Types.goal_env g in
                             let uu___8 = FStarC_Tactics_Types.goal_type g in
                             getprop uu___7 uu___8 in
                           match uu___6 with
                           | FStar_Pervasives_Native.Some vc ->
                               ((let uu___8 =
                                   FStarC_Compiler_Effect.op_Bang dbg_Tac in
                                 if uu___8
                                 then
                                   let uu___9 =
                                     FStarC_Class_Show.show
                                       FStarC_Syntax_Print.showable_term vc in
                                   FStarC_Compiler_Util.print1
                                     "Synthesis left a goal: %s\n" uu___9
                                 else ());
                                if
                                  Prims.op_Negation
                                    env.FStarC_TypeChecker_Env.admit
                                then
                                  (let guard =
                                     FStarC_TypeChecker_Env.guard_of_guard_formula
                                       (FStarC_TypeChecker_Common.NonTrivial
                                          vc) in
                                   FStarC_Profiling.profile
                                     (fun uu___8 ->
                                        let uu___9 =
                                          FStarC_Tactics_Types.goal_env g in
                                        FStarC_TypeChecker_Rel.force_trivial_guard
                                          uu___9 guard)
                                     FStar_Pervasives_Native.None
                                     "FStarC.TypeChecker.Hooks.force_trivial_guard")
                                else ())
                           | FStar_Pervasives_Native.None ->
                               FStarC_Errors.raise_error
                                 FStarC_TypeChecker_Env.hasRange_env env
                                 FStarC_Errors_Codes.Fatal_OpenGoalsInSynthesis
                                 ()
                                 (Obj.magic
                                    FStarC_Errors_Msg.is_error_message_string)
                                 (Obj.magic "synthesis left open goals"))) gs)))
let (find_user_tac_for_attr :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env ->
    fun a ->
      let hooks =
        FStarC_TypeChecker_Env.lookup_attr env
          FStarC_Parser_Const.handle_smt_goals_attr_string in
      FStarC_Compiler_Util.try_find (fun uu___ -> true) hooks
let (handle_smt_goal :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Env.goal ->
      (FStarC_TypeChecker_Env.env * FStarC_Syntax_Syntax.term) Prims.list)
  =
  fun env ->
    fun goal ->
      let uu___ = FStarC_TypeChecker_Common.check_trivial goal in
      match uu___ with
      | FStarC_TypeChecker_Common.Trivial -> [(env, goal)]
      | FStarC_TypeChecker_Common.NonTrivial goal1 ->
          let uu___1 =
            let uu___2 =
              FStarC_Syntax_Syntax.tconst
                FStarC_Parser_Const.handle_smt_goals_attr in
            find_user_tac_for_attr env uu___2 in
          (match uu___1 with
           | FStar_Pervasives_Native.Some tac ->
               let tau =
                 match tac.FStarC_Syntax_Syntax.sigel with
                 | FStarC_Syntax_Syntax.Sig_let
                     { FStarC_Syntax_Syntax.lbs1 = uu___2;
                       FStarC_Syntax_Syntax.lids1 = lid::[];_}
                     ->
                     let qn = FStarC_TypeChecker_Env.lookup_qname env lid in
                     let fv =
                       FStarC_Syntax_Syntax.lid_as_fv lid
                         FStar_Pervasives_Native.None in
                     let uu___3 =
                       FStarC_Syntax_Syntax.lid_as_fv lid
                         FStar_Pervasives_Native.None in
                     FStarC_Syntax_Syntax.fv_to_tm uu___3
                 | uu___2 -> failwith "Resolve_tac not found" in
               let gs =
                 FStarC_Errors.with_ctx
                   "While handling an SMT goal with a tactic"
                   (fun uu___2 ->
                      let uu___3 =
                        let uu___4 = FStarC_TypeChecker_Env.get_range env in
                        let uu___5 =
                          FStarC_Syntax_Util.mk_squash
                            FStarC_Syntax_Syntax.U_zero goal1 in
                        run_tactic_on_typ tau.FStarC_Syntax_Syntax.pos uu___4
                          tau env uu___5 in
                      match uu___3 with
                      | (gs1, uu___4) ->
                          FStarC_Compiler_List.map
                            (fun g ->
                               let uu___5 =
                                 let uu___6 = FStarC_Tactics_Types.goal_env g in
                                 let uu___7 =
                                   FStarC_Tactics_Types.goal_type g in
                                 getprop uu___6 uu___7 in
                               match uu___5 with
                               | FStar_Pervasives_Native.Some vc ->
                                   ((let uu___7 =
                                       FStarC_Compiler_Effect.op_Bang dbg_Tac in
                                     if uu___7
                                     then
                                       let uu___8 =
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Print.showable_term
                                           vc in
                                       FStarC_Compiler_Util.print1
                                         "handle_smt_goals left a goal: %s\n"
                                         uu___8
                                     else ());
                                    (let uu___7 =
                                       FStarC_Tactics_Types.goal_env g in
                                     (uu___7, vc)))
                               | FStar_Pervasives_Native.None ->
                                   FStarC_Errors.raise_error
                                     FStarC_TypeChecker_Env.hasRange_env env
                                     FStarC_Errors_Codes.Fatal_OpenGoalsInSynthesis
                                     ()
                                     (Obj.magic
                                        FStarC_Errors_Msg.is_error_message_string)
                                     (Obj.magic
                                        "Handling an SMT goal by tactic left non-prop open goals"))
                            gs1) in
               gs
           | FStar_Pervasives_Native.None -> [(env, goal1)])
let (uu___0 :
  FStarC_Syntax_Syntax.term FStarC_Syntax_Embeddings_Base.embedding) =
  FStarC_Reflection_V2_Embeddings.e_term
type blob_t =
  (Prims.string * FStarC_Syntax_Syntax.term) FStar_Pervasives_Native.option
type dsl_typed_sigelt_t = (Prims.bool * FStarC_Syntax_Syntax.sigelt * blob_t)
type dsl_tac_result_t =
  (dsl_typed_sigelt_t Prims.list * dsl_typed_sigelt_t * dsl_typed_sigelt_t
    Prims.list)
let (splice :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      FStarC_Ident.lident Prims.list ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Compiler_Range_Type.range ->
            FStarC_Syntax_Syntax.sigelt Prims.list)
  =
  fun env ->
    fun is_typed ->
      fun lids ->
        fun tau ->
          fun rng ->
            FStarC_Errors.with_ctx "While running splice with a tactic"
              (fun uu___ ->
                 if env.FStarC_TypeChecker_Env.flychecking
                 then []
                 else
                   (let uu___2 =
                      if is_typed
                      then
                        FStarC_TypeChecker_TcTerm.tc_check_tot_or_gtot_term
                          env tau FStarC_Syntax_Util.t_dsl_tac_typ
                          FStar_Pervasives_Native.None
                      else
                        FStarC_TypeChecker_TcTerm.tc_tactic
                          FStarC_Syntax_Syntax.t_unit
                          FStarC_Syntax_Syntax.t_decls env tau in
                    match uu___2 with
                    | (tau1, uu___3, g) ->
                        (FStarC_TypeChecker_Rel.force_trivial_guard env g;
                         (let ps =
                            FStarC_Tactics_V2_Basic.proofstate_of_goals
                              tau1.FStarC_Syntax_Syntax.pos env [] [] in
                          let tactic_already_typed = true in
                          let uu___5 =
                            if is_typed
                            then
                              (if
                                 (FStarC_Compiler_List.length lids) >
                                   Prims.int_one
                               then
                                 let uu___6 =
                                   let uu___7 =
                                     FStarC_Class_Show.show
                                       (FStarC_Class_Show.show_list
                                          FStarC_Ident.showable_lident) lids in
                                   FStarC_Compiler_Util.format1
                                     "Typed splice: unexpected lids length (> 1) (%s)"
                                     uu___7 in
                                 FStarC_Errors.raise_error
                                   FStarC_Class_HasRange.hasRange_range rng
                                   FStarC_Errors_Codes.Error_BadSplice ()
                                   (Obj.magic
                                      FStarC_Errors_Msg.is_error_message_string)
                                   (Obj.magic uu___6)
                               else
                                 (let val_t =
                                    if
                                      (FStarC_Compiler_List.length lids) =
                                        Prims.int_zero
                                    then FStar_Pervasives_Native.None
                                    else
                                      (let uu___8 =
                                         let uu___9 =
                                           FStarC_Compiler_List.hd lids in
                                         FStarC_TypeChecker_Env.try_lookup_val_decl
                                           env uu___9 in
                                       match uu___8 with
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some
                                           ((uvs, tval), uu___9) ->
                                           if
                                             (FStarC_Compiler_List.length uvs)
                                               <> Prims.int_zero
                                           then
                                             let uu___10 =
                                               let uu___11 =
                                                 FStarC_Class_Show.show
                                                   FStarC_Class_Show.showable_nat
                                                   (FStarC_Compiler_List.length
                                                      uvs) in
                                               FStarC_Compiler_Util.format1
                                                 "Typed splice: val declaration for %s is universe polymorphic in %s universes, expected 0"
                                                 uu___11 in
                                             FStarC_Errors.raise_error
                                               FStarC_Class_HasRange.hasRange_range
                                               rng
                                               FStarC_Errors_Codes.Error_BadSplice
                                               ()
                                               (Obj.magic
                                                  FStarC_Errors_Msg.is_error_message_string)
                                               (Obj.magic uu___10)
                                           else
                                             FStar_Pervasives_Native.Some
                                               tval) in
                                  let uu___7 =
                                    FStarC_Tactics_Interpreter.run_tactic_on_ps
                                      tau1.FStarC_Syntax_Syntax.pos
                                      tau1.FStarC_Syntax_Syntax.pos false
                                      (FStarC_Syntax_Embeddings.e_tuple2
                                         FStarC_Reflection_V2_Embeddings.e_env
                                         (FStarC_Syntax_Embeddings.e_option
                                            uu___0))
                                      ({
                                         FStarC_TypeChecker_Env.solver =
                                           (env.FStarC_TypeChecker_Env.solver);
                                         FStarC_TypeChecker_Env.range =
                                           (env.FStarC_TypeChecker_Env.range);
                                         FStarC_TypeChecker_Env.curmodule =
                                           (env.FStarC_TypeChecker_Env.curmodule);
                                         FStarC_TypeChecker_Env.gamma = [];
                                         FStarC_TypeChecker_Env.gamma_sig =
                                           (env.FStarC_TypeChecker_Env.gamma_sig);
                                         FStarC_TypeChecker_Env.gamma_cache =
                                           (env.FStarC_TypeChecker_Env.gamma_cache);
                                         FStarC_TypeChecker_Env.modules =
                                           (env.FStarC_TypeChecker_Env.modules);
                                         FStarC_TypeChecker_Env.expected_typ
                                           =
                                           (env.FStarC_TypeChecker_Env.expected_typ);
                                         FStarC_TypeChecker_Env.sigtab =
                                           (env.FStarC_TypeChecker_Env.sigtab);
                                         FStarC_TypeChecker_Env.attrtab =
                                           (env.FStarC_TypeChecker_Env.attrtab);
                                         FStarC_TypeChecker_Env.instantiate_imp
                                           =
                                           (env.FStarC_TypeChecker_Env.instantiate_imp);
                                         FStarC_TypeChecker_Env.effects =
                                           (env.FStarC_TypeChecker_Env.effects);
                                         FStarC_TypeChecker_Env.generalize =
                                           (env.FStarC_TypeChecker_Env.generalize);
                                         FStarC_TypeChecker_Env.letrecs =
                                           (env.FStarC_TypeChecker_Env.letrecs);
                                         FStarC_TypeChecker_Env.top_level =
                                           (env.FStarC_TypeChecker_Env.top_level);
                                         FStarC_TypeChecker_Env.check_uvars =
                                           (env.FStarC_TypeChecker_Env.check_uvars);
                                         FStarC_TypeChecker_Env.use_eq_strict
                                           =
                                           (env.FStarC_TypeChecker_Env.use_eq_strict);
                                         FStarC_TypeChecker_Env.is_iface =
                                           (env.FStarC_TypeChecker_Env.is_iface);
                                         FStarC_TypeChecker_Env.admit = false;
                                         FStarC_TypeChecker_Env.lax_universes
                                           =
                                           (env.FStarC_TypeChecker_Env.lax_universes);
                                         FStarC_TypeChecker_Env.phase1 =
                                           (env.FStarC_TypeChecker_Env.phase1);
                                         FStarC_TypeChecker_Env.failhard =
                                           (env.FStarC_TypeChecker_Env.failhard);
                                         FStarC_TypeChecker_Env.flychecking =
                                           (env.FStarC_TypeChecker_Env.flychecking);
                                         FStarC_TypeChecker_Env.uvar_subtyping
                                           =
                                           (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                         FStarC_TypeChecker_Env.intactics =
                                           (env.FStarC_TypeChecker_Env.intactics);
                                         FStarC_TypeChecker_Env.nocoerce =
                                           (env.FStarC_TypeChecker_Env.nocoerce);
                                         FStarC_TypeChecker_Env.tc_term =
                                           (env.FStarC_TypeChecker_Env.tc_term);
                                         FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                           =
                                           (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                         FStarC_TypeChecker_Env.universe_of =
                                           (env.FStarC_TypeChecker_Env.universe_of);
                                         FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                           =
                                           (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                         FStarC_TypeChecker_Env.teq_nosmt_force
                                           =
                                           (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                         FStarC_TypeChecker_Env.subtype_nosmt_force
                                           =
                                           (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                         FStarC_TypeChecker_Env.qtbl_name_and_index
                                           =
                                           (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                         FStarC_TypeChecker_Env.normalized_eff_names
                                           =
                                           (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                         FStarC_TypeChecker_Env.fv_delta_depths
                                           =
                                           (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                         FStarC_TypeChecker_Env.proof_ns =
                                           (env.FStarC_TypeChecker_Env.proof_ns);
                                         FStarC_TypeChecker_Env.synth_hook =
                                           (env.FStarC_TypeChecker_Env.synth_hook);
                                         FStarC_TypeChecker_Env.try_solve_implicits_hook
                                           =
                                           (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                         FStarC_TypeChecker_Env.splice =
                                           (env.FStarC_TypeChecker_Env.splice);
                                         FStarC_TypeChecker_Env.mpreprocess =
                                           (env.FStarC_TypeChecker_Env.mpreprocess);
                                         FStarC_TypeChecker_Env.postprocess =
                                           (env.FStarC_TypeChecker_Env.postprocess);
                                         FStarC_TypeChecker_Env.identifier_info
                                           =
                                           (env.FStarC_TypeChecker_Env.identifier_info);
                                         FStarC_TypeChecker_Env.tc_hooks =
                                           (env.FStarC_TypeChecker_Env.tc_hooks);
                                         FStarC_TypeChecker_Env.dsenv =
                                           (env.FStarC_TypeChecker_Env.dsenv);
                                         FStarC_TypeChecker_Env.nbe =
                                           (env.FStarC_TypeChecker_Env.nbe);
                                         FStarC_TypeChecker_Env.strict_args_tab
                                           =
                                           (env.FStarC_TypeChecker_Env.strict_args_tab);
                                         FStarC_TypeChecker_Env.erasable_types_tab
                                           =
                                           (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                         FStarC_TypeChecker_Env.enable_defer_to_tac
                                           =
                                           (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                         FStarC_TypeChecker_Env.unif_allow_ref_guards
                                           =
                                           (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                         FStarC_TypeChecker_Env.erase_erasable_args
                                           =
                                           (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                         FStarC_TypeChecker_Env.core_check =
                                           (env.FStarC_TypeChecker_Env.core_check);
                                         FStarC_TypeChecker_Env.missing_decl
                                           =
                                           (env.FStarC_TypeChecker_Env.missing_decl)
                                       }, val_t)
                                      (FStarC_Syntax_Embeddings.e_tuple3
                                         (FStarC_Syntax_Embeddings.e_list
                                            (FStarC_Syntax_Embeddings.e_tuple3
                                               FStarC_Syntax_Embeddings.e_bool
                                               FStarC_Reflection_V2_Embeddings.e_sigelt
                                               (FStarC_Syntax_Embeddings.e_option
                                                  (FStarC_Syntax_Embeddings.e_tuple2
                                                     FStarC_Syntax_Embeddings.e_string
                                                     uu___0))))
                                         (FStarC_Syntax_Embeddings.e_tuple3
                                            FStarC_Syntax_Embeddings.e_bool
                                            FStarC_Reflection_V2_Embeddings.e_sigelt
                                            (FStarC_Syntax_Embeddings.e_option
                                               (FStarC_Syntax_Embeddings.e_tuple2
                                                  FStarC_Syntax_Embeddings.e_string
                                                  uu___0)))
                                         (FStarC_Syntax_Embeddings.e_list
                                            (FStarC_Syntax_Embeddings.e_tuple3
                                               FStarC_Syntax_Embeddings.e_bool
                                               FStarC_Reflection_V2_Embeddings.e_sigelt
                                               (FStarC_Syntax_Embeddings.e_option
                                                  (FStarC_Syntax_Embeddings.e_tuple2
                                                     FStarC_Syntax_Embeddings.e_string
                                                     uu___0))))) tau1
                                      tactic_already_typed ps in
                                  match uu___7 with
                                  | (gs,
                                     (sig_blobs_before, sig_blob,
                                      sig_blobs_after)) ->
                                      let uu___8 = uu___7 in
                                      let sig_blobs =
                                        FStarC_Compiler_List.op_At
                                          sig_blobs_before (sig_blob ::
                                          sig_blobs_after) in
                                      let sigelts =
                                        FStarC_Compiler_List.map
                                          (fun uu___9 ->
                                             match uu___9 with
                                             | (checked, se, blob_opt) ->
                                                 let uu___10 =
                                                   let uu___11 =
                                                     se.FStarC_Syntax_Syntax.sigmeta in
                                                   let uu___12 =
                                                     match blob_opt with
                                                     | FStar_Pervasives_Native.Some
                                                         (s, blob) ->
                                                         let uu___13 =
                                                           let uu___14 =
                                                             FStarC_Dyn.mkdyn
                                                               blob in
                                                           (s, uu___14) in
                                                         [uu___13]
                                                     | FStar_Pervasives_Native.None
                                                         -> [] in
                                                   {
                                                     FStarC_Syntax_Syntax.sigmeta_active
                                                       =
                                                       (uu___11.FStarC_Syntax_Syntax.sigmeta_active);
                                                     FStarC_Syntax_Syntax.sigmeta_fact_db_ids
                                                       =
                                                       (uu___11.FStarC_Syntax_Syntax.sigmeta_fact_db_ids);
                                                     FStarC_Syntax_Syntax.sigmeta_admit
                                                       =
                                                       (uu___11.FStarC_Syntax_Syntax.sigmeta_admit);
                                                     FStarC_Syntax_Syntax.sigmeta_spliced
                                                       =
                                                       (uu___11.FStarC_Syntax_Syntax.sigmeta_spliced);
                                                     FStarC_Syntax_Syntax.sigmeta_already_checked
                                                       = checked;
                                                     FStarC_Syntax_Syntax.sigmeta_extension_data
                                                       = uu___12
                                                   } in
                                                 {
                                                   FStarC_Syntax_Syntax.sigel
                                                     =
                                                     (se.FStarC_Syntax_Syntax.sigel);
                                                   FStarC_Syntax_Syntax.sigrng
                                                     =
                                                     (se.FStarC_Syntax_Syntax.sigrng);
                                                   FStarC_Syntax_Syntax.sigquals
                                                     =
                                                     (se.FStarC_Syntax_Syntax.sigquals);
                                                   FStarC_Syntax_Syntax.sigmeta
                                                     = uu___10;
                                                   FStarC_Syntax_Syntax.sigattrs
                                                     =
                                                     (se.FStarC_Syntax_Syntax.sigattrs);
                                                   FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                                     =
                                                     (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                                   FStarC_Syntax_Syntax.sigopts
                                                     =
                                                     (se.FStarC_Syntax_Syntax.sigopts)
                                                 }) sig_blobs in
                                      (gs, sigelts)))
                            else
                              FStarC_Tactics_Interpreter.run_tactic_on_ps
                                tau1.FStarC_Syntax_Syntax.pos
                                tau1.FStarC_Syntax_Syntax.pos false
                                FStarC_Syntax_Embeddings.e_unit ()
                                (FStarC_Syntax_Embeddings.e_list
                                   FStarC_Reflection_V2_Embeddings.e_sigelt)
                                tau1 tactic_already_typed ps in
                          match uu___5 with
                          | (gs, sigelts) ->
                              let sigelts1 =
                                let set_lb_dd lb =
                                  let uu___6 = lb in
                                  match uu___6 with
                                  | {
                                      FStarC_Syntax_Syntax.lbname =
                                        FStar_Pervasives.Inr fv;
                                      FStarC_Syntax_Syntax.lbunivs = uu___7;
                                      FStarC_Syntax_Syntax.lbtyp = uu___8;
                                      FStarC_Syntax_Syntax.lbeff = uu___9;
                                      FStarC_Syntax_Syntax.lbdef = lbdef;
                                      FStarC_Syntax_Syntax.lbattrs = uu___10;
                                      FStarC_Syntax_Syntax.lbpos = uu___11;_}
                                      ->
                                      {
                                        FStarC_Syntax_Syntax.lbname =
                                          (FStar_Pervasives.Inr fv);
                                        FStarC_Syntax_Syntax.lbunivs =
                                          (lb.FStarC_Syntax_Syntax.lbunivs);
                                        FStarC_Syntax_Syntax.lbtyp =
                                          (lb.FStarC_Syntax_Syntax.lbtyp);
                                        FStarC_Syntax_Syntax.lbeff =
                                          (lb.FStarC_Syntax_Syntax.lbeff);
                                        FStarC_Syntax_Syntax.lbdef =
                                          (lb.FStarC_Syntax_Syntax.lbdef);
                                        FStarC_Syntax_Syntax.lbattrs =
                                          (lb.FStarC_Syntax_Syntax.lbattrs);
                                        FStarC_Syntax_Syntax.lbpos =
                                          (lb.FStarC_Syntax_Syntax.lbpos)
                                      } in
                                FStarC_Compiler_List.map
                                  (fun se ->
                                     match se.FStarC_Syntax_Syntax.sigel with
                                     | FStarC_Syntax_Syntax.Sig_let
                                         {
                                           FStarC_Syntax_Syntax.lbs1 =
                                             (is_rec, lbs);
                                           FStarC_Syntax_Syntax.lids1 = lids1;_}
                                         ->
                                         let uu___6 =
                                           let uu___7 =
                                             let uu___8 =
                                               let uu___9 =
                                                 FStarC_Compiler_List.map
                                                   set_lb_dd lbs in
                                               (is_rec, uu___9) in
                                             {
                                               FStarC_Syntax_Syntax.lbs1 =
                                                 uu___8;
                                               FStarC_Syntax_Syntax.lids1 =
                                                 lids1
                                             } in
                                           FStarC_Syntax_Syntax.Sig_let
                                             uu___7 in
                                         {
                                           FStarC_Syntax_Syntax.sigel =
                                             uu___6;
                                           FStarC_Syntax_Syntax.sigrng =
                                             (se.FStarC_Syntax_Syntax.sigrng);
                                           FStarC_Syntax_Syntax.sigquals =
                                             (se.FStarC_Syntax_Syntax.sigquals);
                                           FStarC_Syntax_Syntax.sigmeta =
                                             (se.FStarC_Syntax_Syntax.sigmeta);
                                           FStarC_Syntax_Syntax.sigattrs =
                                             (se.FStarC_Syntax_Syntax.sigattrs);
                                           FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                             =
                                             (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                           FStarC_Syntax_Syntax.sigopts =
                                             (se.FStarC_Syntax_Syntax.sigopts)
                                         }
                                     | uu___6 -> se) sigelts in
                              (FStarC_Options.with_saved_options
                                 (fun uu___7 ->
                                    FStarC_Compiler_List.iter
                                      (fun g1 ->
                                         (let uu___9 =
                                            FStarC_Tactics_Types.goal_opts g1 in
                                          FStarC_Options.set uu___9);
                                         (let uu___9 =
                                            let uu___10 =
                                              FStarC_Tactics_Types.goal_env
                                                g1 in
                                            let uu___11 =
                                              FStarC_Tactics_Types.goal_type
                                                g1 in
                                            getprop uu___10 uu___11 in
                                          match uu___9 with
                                          | FStar_Pervasives_Native.Some vc
                                              ->
                                              ((let uu___11 =
                                                  FStarC_Compiler_Effect.op_Bang
                                                    dbg_Tac in
                                                if uu___11
                                                then
                                                  let uu___12 =
                                                    FStarC_Class_Show.show
                                                      FStarC_Syntax_Print.showable_term
                                                      vc in
                                                  FStarC_Compiler_Util.print1
                                                    "Splice left a goal: %s\n"
                                                    uu___12
                                                else ());
                                               (let guard =
                                                  FStarC_TypeChecker_Env.guard_of_guard_formula
                                                    (FStarC_TypeChecker_Common.NonTrivial
                                                       vc) in
                                                let uu___11 =
                                                  FStarC_Tactics_Types.goal_env
                                                    g1 in
                                                FStarC_TypeChecker_Rel.force_trivial_guard
                                                  uu___11 guard))
                                          | FStar_Pervasives_Native.None ->
                                              FStarC_Errors.raise_error
                                                FStarC_Class_HasRange.hasRange_range
                                                rng
                                                FStarC_Errors_Codes.Fatal_OpenGoalsInSynthesis
                                                ()
                                                (Obj.magic
                                                   FStarC_Errors_Msg.is_error_message_string)
                                                (Obj.magic
                                                   "splice left open goals")))
                                      gs);
                               (let lids' =
                                  FStarC_Compiler_List.collect
                                    FStarC_Syntax_Util.lids_of_sigelt
                                    sigelts1 in
                                FStarC_Compiler_List.iter
                                  (fun lid ->
                                     let uu___8 =
                                       FStarC_Compiler_List.tryFind
                                         (FStarC_Ident.lid_equals lid) lids' in
                                     match uu___8 with
                                     | FStar_Pervasives_Native.None when
                                         Prims.op_Negation
                                           env.FStarC_TypeChecker_Env.flychecking
                                         ->
                                         let uu___9 =
                                           let uu___10 =
                                             FStarC_Class_Show.show
                                               FStarC_Ident.showable_lident
                                               lid in
                                           let uu___11 =
                                             FStarC_Class_Show.show
                                               (FStarC_Class_Show.show_list
                                                  FStarC_Ident.showable_lident)
                                               lids' in
                                           FStarC_Compiler_Util.format2
                                             "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                             uu___10 uu___11 in
                                         FStarC_Errors.raise_error
                                           FStarC_Class_HasRange.hasRange_range
                                           rng
                                           FStarC_Errors_Codes.Fatal_SplicedUndef
                                           ()
                                           (Obj.magic
                                              FStarC_Errors_Msg.is_error_message_string)
                                           (Obj.magic uu___9)
                                     | uu___9 -> ()) lids;
                                (let uu___9 =
                                   FStarC_Compiler_Effect.op_Bang dbg_Tac in
                                 if uu___9
                                 then
                                   let uu___10 =
                                     FStarC_Class_Show.show
                                       (FStarC_Class_Show.show_list
                                          FStarC_Syntax_Print.showable_sigelt)
                                       sigelts1 in
                                   FStarC_Compiler_Util.print1
                                     "splice: got decls = {\n\n%s\n\n}\n"
                                     uu___10
                                 else ());
                                (let sigelts2 =
                                   FStarC_Compiler_List.map
                                     (fun se ->
                                        (match se.FStarC_Syntax_Syntax.sigel
                                         with
                                         | FStarC_Syntax_Syntax.Sig_datacon
                                             uu___10 ->
                                             let uu___11 =
                                               let uu___12 =
                                                 let uu___13 =
                                                   FStarC_Errors_Msg.text
                                                     "Tactic returned bad sigelt:" in
                                                 let uu___14 =
                                                   let uu___15 =
                                                     FStarC_Syntax_Print.sigelt_to_string_short
                                                       se in
                                                   FStarC_Pprint.doc_of_string
                                                     uu___15 in
                                                 FStarC_Pprint.op_Hat_Slash_Hat
                                                   uu___13 uu___14 in
                                               let uu___13 =
                                                 let uu___14 =
                                                   FStarC_Errors_Msg.text
                                                     "If you wanted to splice an inductive type, call `pack` providing a `Sg_Inductive` to get a proper sigelt." in
                                                 [uu___14] in
                                               uu___12 :: uu___13 in
                                             FStarC_Errors.raise_error
                                               FStarC_Class_HasRange.hasRange_range
                                               rng
                                               FStarC_Errors_Codes.Error_BadSplice
                                               ()
                                               (Obj.magic
                                                  FStarC_Errors_Msg.is_error_message_list_doc)
                                               (Obj.magic uu___11)
                                         | FStarC_Syntax_Syntax.Sig_inductive_typ
                                             uu___10 ->
                                             let uu___11 =
                                               let uu___12 =
                                                 let uu___13 =
                                                   FStarC_Errors_Msg.text
                                                     "Tactic returned bad sigelt:" in
                                                 let uu___14 =
                                                   let uu___15 =
                                                     FStarC_Syntax_Print.sigelt_to_string_short
                                                       se in
                                                   FStarC_Pprint.doc_of_string
                                                     uu___15 in
                                                 FStarC_Pprint.op_Hat_Slash_Hat
                                                   uu___13 uu___14 in
                                               let uu___13 =
                                                 let uu___14 =
                                                   FStarC_Errors_Msg.text
                                                     "If you wanted to splice an inductive type, call `pack` providing a `Sg_Inductive` to get a proper sigelt." in
                                                 [uu___14] in
                                               uu___12 :: uu___13 in
                                             FStarC_Errors.raise_error
                                               FStarC_Class_HasRange.hasRange_range
                                               rng
                                               FStarC_Errors_Codes.Error_BadSplice
                                               ()
                                               (Obj.magic
                                                  FStarC_Errors_Msg.is_error_message_list_doc)
                                               (Obj.magic uu___11)
                                         | uu___10 -> ());
                                        {
                                          FStarC_Syntax_Syntax.sigel =
                                            (se.FStarC_Syntax_Syntax.sigel);
                                          FStarC_Syntax_Syntax.sigrng = rng;
                                          FStarC_Syntax_Syntax.sigquals =
                                            (se.FStarC_Syntax_Syntax.sigquals);
                                          FStarC_Syntax_Syntax.sigmeta =
                                            (se.FStarC_Syntax_Syntax.sigmeta);
                                          FStarC_Syntax_Syntax.sigattrs =
                                            (se.FStarC_Syntax_Syntax.sigattrs);
                                          FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                            =
                                            (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                          FStarC_Syntax_Syntax.sigopts =
                                            (se.FStarC_Syntax_Syntax.sigopts)
                                        }) sigelts1 in
                                 if is_typed
                                 then ()
                                 else
                                   FStarC_Compiler_List.iter
                                     (fun se ->
                                        FStarC_Compiler_List.iter
                                          (fun q ->
                                             let uu___11 =
                                               FStarC_Syntax_Syntax.is_internal_qualifier
                                                 q in
                                             if uu___11
                                             then
                                               let uu___12 =
                                                 let uu___13 =
                                                   let uu___14 =
                                                     let uu___15 =
                                                       FStarC_Class_Show.show
                                                         FStarC_Syntax_Print.showable_qualifier
                                                         q in
                                                     FStarC_Compiler_Util.format1
                                                       "The qualifier %s is internal."
                                                       uu___15 in
                                                   FStarC_Errors_Msg.text
                                                     uu___14 in
                                                 let uu___14 =
                                                   let uu___15 =
                                                     let uu___16 =
                                                       FStarC_Errors_Msg.text
                                                         "It cannot be attached to spliced declaration:" in
                                                     let uu___17 =
                                                       let uu___18 =
                                                         FStarC_Syntax_Print.sigelt_to_string_short
                                                           se in
                                                       FStarC_Pprint.arbitrary_string
                                                         uu___18 in
                                                     FStarC_Pprint.prefix
                                                       (Prims.of_int (2))
                                                       Prims.int_one uu___16
                                                       uu___17 in
                                                   [uu___15] in
                                                 uu___13 :: uu___14 in
                                               FStarC_Errors.raise_error
                                                 FStarC_Class_HasRange.hasRange_range
                                                 rng
                                                 FStarC_Errors_Codes.Error_InternalQualifier
                                                 ()
                                                 (Obj.magic
                                                    FStarC_Errors_Msg.is_error_message_list_doc)
                                                 (Obj.magic uu___12)
                                             else ())
                                          se.FStarC_Syntax_Syntax.sigquals)
                                     sigelts2;
                                 (match () with | () -> sigelts2))))))))
let (mpreprocess :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun tau ->
      fun tm ->
        FStarC_Errors.with_ctx
          "While preprocessing a definition with a tactic"
          (fun uu___ ->
             if env.FStarC_TypeChecker_Env.flychecking
             then tm
             else
               (let ps =
                  FStarC_Tactics_V2_Basic.proofstate_of_goals
                    tm.FStarC_Syntax_Syntax.pos env [] [] in
                let tactic_already_typed = false in
                let uu___2 =
                  FStarC_Tactics_Interpreter.run_tactic_on_ps
                    tau.FStarC_Syntax_Syntax.pos tm.FStarC_Syntax_Syntax.pos
                    false FStarC_Reflection_V2_Embeddings.e_term tm
                    FStarC_Reflection_V2_Embeddings.e_term tau
                    tactic_already_typed ps in
                match uu___2 with | (gs, tm1) -> tm1))
let (postprocess :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun tau ->
      fun typ ->
        fun tm ->
          FStarC_Errors.with_ctx
            "While postprocessing a definition with a tactic"
            (fun uu___ ->
               if env.FStarC_TypeChecker_Env.flychecking
               then tm
               else
                 (let uu___2 =
                    FStarC_TypeChecker_Env.new_implicit_var_aux
                      "postprocess RHS" tm.FStarC_Syntax_Syntax.pos env typ
                      (FStarC_Syntax_Syntax.Allow_untyped "postprocess")
                      FStar_Pervasives_Native.None false in
                  match uu___2 with
                  | (uvtm, uu___3, g_imp) ->
                      let u = env.FStarC_TypeChecker_Env.universe_of env typ in
                      let goal =
                        let uu___4 = FStarC_Syntax_Util.mk_eq2 u typ tm uvtm in
                        FStarC_Syntax_Util.mk_squash
                          FStarC_Syntax_Syntax.U_zero uu___4 in
                      let uu___4 =
                        run_tactic_on_typ tau.FStarC_Syntax_Syntax.pos
                          tm.FStarC_Syntax_Syntax.pos tau env goal in
                      (match uu___4 with
                       | (gs, w) ->
                           (FStarC_Compiler_List.iter
                              (fun g ->
                                 let uu___6 =
                                   let uu___7 =
                                     FStarC_Tactics_Types.goal_env g in
                                   let uu___8 =
                                     FStarC_Tactics_Types.goal_type g in
                                   getprop uu___7 uu___8 in
                                 match uu___6 with
                                 | FStar_Pervasives_Native.Some vc ->
                                     ((let uu___8 =
                                         FStarC_Compiler_Effect.op_Bang
                                           dbg_Tac in
                                       if uu___8
                                       then
                                         let uu___9 =
                                           FStarC_Class_Show.show
                                             FStarC_Syntax_Print.showable_term
                                             vc in
                                         FStarC_Compiler_Util.print1
                                           "Postprocessing left a goal: %s\n"
                                           uu___9
                                       else ());
                                      (let guard =
                                         FStarC_TypeChecker_Env.guard_of_guard_formula
                                           (FStarC_TypeChecker_Common.NonTrivial
                                              vc) in
                                       let uu___8 =
                                         FStarC_Tactics_Types.goal_env g in
                                       FStarC_TypeChecker_Rel.force_trivial_guard
                                         uu___8 guard))
                                 | FStar_Pervasives_Native.None ->
                                     FStarC_Errors.raise_error
                                       (FStarC_Syntax_Syntax.has_range_syntax
                                          ()) typ
                                       FStarC_Errors_Codes.Fatal_OpenGoalsInSynthesis
                                       ()
                                       (Obj.magic
                                          FStarC_Errors_Msg.is_error_message_string)
                                       (Obj.magic
                                          "postprocessing left open goals"))
                              gs;
                            (let tagged_imps =
                               FStarC_TypeChecker_Rel.resolve_implicits_tac
                                 env g_imp in
                             FStarC_Tactics_Interpreter.report_implicits
                               tm.FStarC_Syntax_Syntax.pos tagged_imps;
                             uvtm)))))