open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> normalize [] e t
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> FStar_TypeChecker_Normalize.unfold_whnf e t
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun e ->
    fun t ->
      FStar_Syntax_Print.term_to_string' e.FStar_TypeChecker_Env.dsenv t
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g ->
    let uu____58 =
      let uu____59 = FStar_Tactics_Types.goal_env g in
      let uu____60 = FStar_Tactics_Types.goal_type g in
      bnorm uu____59 uu____60 in
    FStar_Tactics_Types.goal_with_type g uu____58
let (tacprint : Prims.string -> unit) =
  fun s -> FStar_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu____76 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____76
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu____92 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____92
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu____113 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____113
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    (let uu____124 =
       let uu____125 = FStar_Options.silent () in Prims.op_Negation uu____125 in
     if uu____124 then tacprint msg else ());
    FStar_Tactics_Monad.ret ()
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____133 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let uu____139 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac") in
         FStar_Tactics_Monad.ret uu____139)
let (do_dump_ps : Prims.string -> FStar_Tactics_Types.proofstate -> unit) =
  fun msg ->
    fun ps ->
      let psc = ps.FStar_Tactics_Types.psc in
      let subst = FStar_TypeChecker_Cfg.psc_subst psc in
      let uu____152 = FStar_Tactics_Types.subst_proof_state subst ps in
      FStar_Tactics_Printing.do_dump_proofstate uu____152 msg
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    FStar_Tactics_Monad.mk_tac
      (fun ps -> do_dump_ps msg ps; FStar_Tactics_Result.Success ((), ps))
let (dump_all : Prims.bool -> Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun print_resolved ->
    fun msg ->
      FStar_Tactics_Monad.mk_tac
        (fun ps ->
           let gs =
             FStar_List.map
               (fun i ->
                  FStar_Tactics_Types.goal_of_implicit
                    ps.FStar_Tactics_Types.main_context i)
               ps.FStar_Tactics_Types.all_implicits in
           let gs1 =
             if print_resolved
             then gs
             else
               FStar_List.filter
                 (fun g ->
                    let uu____200 = FStar_Tactics_Types.check_goal_solved g in
                    Prims.op_Negation uu____200) gs in
           let ps' =
             let uu___49_202 = ps in
             {
               FStar_Tactics_Types.main_context =
                 (uu___49_202.FStar_Tactics_Types.main_context);
               FStar_Tactics_Types.all_implicits =
                 (uu___49_202.FStar_Tactics_Types.all_implicits);
               FStar_Tactics_Types.goals = gs1;
               FStar_Tactics_Types.smt_goals = [];
               FStar_Tactics_Types.depth =
                 (uu___49_202.FStar_Tactics_Types.depth);
               FStar_Tactics_Types.__dump =
                 (uu___49_202.FStar_Tactics_Types.__dump);
               FStar_Tactics_Types.psc =
                 (uu___49_202.FStar_Tactics_Types.psc);
               FStar_Tactics_Types.entry_range =
                 (uu___49_202.FStar_Tactics_Types.entry_range);
               FStar_Tactics_Types.guard_policy =
                 (uu___49_202.FStar_Tactics_Types.guard_policy);
               FStar_Tactics_Types.freshness =
                 (uu___49_202.FStar_Tactics_Types.freshness);
               FStar_Tactics_Types.tac_verb_dbg =
                 (uu___49_202.FStar_Tactics_Types.tac_verb_dbg);
               FStar_Tactics_Types.local_state =
                 (uu___49_202.FStar_Tactics_Types.local_state)
             } in
           do_dump_ps msg ps'; FStar_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuuu210 .
    Prims.string -> Prims.string -> 'uuuuuu210 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      let uu____223 = FStar_Util.format1 msg x in
      FStar_Tactics_Monad.fail uu____223
let fail2 :
  'uuuuuu232 .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuuu232 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu____250 = FStar_Util.format2 msg x y in
        FStar_Tactics_Monad.fail uu____250
let fail3 :
  'uuuuuu261 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuuu261 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu____284 = FStar_Util.format3 msg x y z in
          FStar_Tactics_Monad.fail uu____284
let fail4 :
  'uuuuuu297 .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuuu297 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu____325 = FStar_Util.format4 msg x y z w in
            FStar_Tactics_Monad.fail uu____325
let catch :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____358 = FStar_Tactics_Monad.run t ps in
         match uu____358 with
         | FStar_Tactics_Result.Success (a1, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___82_382 = ps in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___82_382.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___82_382.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___82_382.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___82_382.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___82_382.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___82_382.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___82_382.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___82_382.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___82_382.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___82_382.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___82_382.FStar_Tactics_Types.local_state)
                 } in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
let recover :
  'a .
    'a FStar_Tactics_Monad.tac ->
      (Prims.exn, 'a) FStar_Util.either FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let uu____420 = FStar_Tactics_Monad.run t ps in
         match uu____420 with
         | FStar_Tactics_Result.Success (a1, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q)
         | FStar_Tactics_Result.Failed (m, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
let trytac :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t ->
    let uu____467 = catch t in
    FStar_Tactics_Monad.bind uu____467
      (fun r ->
         match r with
         | FStar_Util.Inr v ->
             FStar_Tactics_Monad.ret (FStar_Pervasives_Native.Some v)
         | FStar_Util.Inl uu____494 ->
             FStar_Tactics_Monad.ret FStar_Pervasives_Native.None)
let trytac_exn :
  'a .
    'a FStar_Tactics_Monad.tac ->
      'a FStar_Pervasives_Native.option FStar_Tactics_Monad.tac
  =
  fun t ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         try
           (fun uu___108_525 ->
              match () with
              | () ->
                  let uu____530 = trytac t in
                  FStar_Tactics_Monad.run uu____530 ps) ()
         with
         | FStar_Errors.Err (uu____546, msg) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____550 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____555, msg, uu____557) ->
             (FStar_Tactics_Monad.log ps
                (fun uu____560 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____582 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____582 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,
         uu____592::(e1, FStar_Pervasives_Native.None)::(e2,
                                                         FStar_Pervasives_Native.None)::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l, uu____652::uu____653::(e1, uu____655)::(e2, uu____657)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____734 ->
        let uu____737 = FStar_Syntax_Util.unb2t typ in
        (match uu____737 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____751 = FStar_Syntax_Util.head_and_args t in
             (match uu____751 with
              | (hd, args) ->
                  let uu____800 =
                    let uu____815 =
                      let uu____816 = FStar_Syntax_Subst.compress hd in
                      uu____816.FStar_Syntax_Syntax.n in
                    (uu____815, args) in
                  (match uu____800 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,
                      (uu____836, FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____837))::(e1,
                                                                   FStar_Pervasives_Native.None)::
                      (e2, FStar_Pervasives_Native.None)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____904 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____940 = destruct_eq' typ in
    match uu____940 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None ->
        let uu____970 = FStar_Syntax_Util.un_squash typ in
        (match uu____970 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        (let uu____1012 =
           FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
         if uu____1012
         then
           let uu____1013 = FStar_Syntax_Print.term_to_string t1 in
           let uu____1014 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1013
             uu____1014
         else ());
        (try
           (fun uu___184_1021 ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env1 t1 t2 in
                  ((let uu____1028 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____1028
                    then
                      let uu____1029 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env1) res in
                      let uu____1030 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____1031 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1029
                        uu____1030 uu____1031
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1036 =
                          FStar_Tactics_Monad.add_implicits
                            g.FStar_TypeChecker_Common.implicits in
                        FStar_Tactics_Monad.bind uu____1036
                          (fun uu____1040 -> FStar_Tactics_Monad.ret true))))
             ()
         with
         | FStar_Errors.Err (uu____1047, msg) ->
             FStar_Tactics_Monad.mlog
               (fun uu____1050 ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1052 -> FStar_Tactics_Monad.ret false)
         | FStar_Errors.Error (uu____1053, msg, r) ->
             FStar_Tactics_Monad.mlog
               (fun uu____1058 ->
                  let uu____1059 = FStar_Range.string_of_range r in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1059)
               (fun uu____1061 -> FStar_Tactics_Monad.ret false))
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____1084 ->
             (let uu____1086 =
                FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "1346") in
              if uu____1086
              then
                (FStar_Options.push ();
                 (let uu____1088 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck" in
                  ()))
              else ());
             (let uu____1090 = __do_unify env1 t1 t2 in
              FStar_Tactics_Monad.bind uu____1090
                (fun r ->
                   (let uu____1097 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "1346") in
                    if uu____1097 then FStar_Options.pop () else ());
                   FStar_Tactics_Monad.ret r)))
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____1118 =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu____1118
          (fun tx ->
             let uvs1 = FStar_Syntax_Free.uvars_uncached t1 in
             let uu____1132 = do_unify env1 t1 t2 in
             FStar_Tactics_Monad.bind uu____1132
               (fun r ->
                  if r
                  then
                    let uvs2 = FStar_Syntax_Free.uvars_uncached t1 in
                    let uu____1145 =
                      let uu____1146 = FStar_Util.set_eq uvs1 uvs2 in
                      Prims.op_Negation uu____1146 in
                    (if uu____1145
                     then
                       (FStar_Syntax_Unionfind.rollback tx;
                        FStar_Tactics_Monad.ret false)
                     else FStar_Tactics_Monad.ret true)
                  else FStar_Tactics_Monad.ret false))
let (do_match_on_lhs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____1171 =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu____1171
          (fun tx ->
             let uu____1181 = destruct_eq t1 in
             match uu____1181 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "do_match_on_lhs: not an eq"
             | FStar_Pervasives_Native.Some (lhs, uu____1195) ->
                 let uvs1 = FStar_Syntax_Free.uvars_uncached lhs in
                 let uu____1203 = do_unify env1 t1 t2 in
                 FStar_Tactics_Monad.bind uu____1203
                   (fun r ->
                      if r
                      then
                        let uvs2 = FStar_Syntax_Free.uvars_uncached lhs in
                        let uu____1216 =
                          let uu____1217 = FStar_Util.set_eq uvs1 uvs2 in
                          Prims.op_Negation uu____1217 in
                        (if uu____1216
                         then
                           (FStar_Syntax_Unionfind.rollback tx;
                            FStar_Tactics_Monad.ret false)
                         else FStar_Tactics_Monad.ret true)
                      else FStar_Tactics_Monad.ret false))
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1237 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu____1237 with
      | FStar_Pervasives_Native.Some uu____1242 ->
          let uu____1243 =
            let uu____1244 =
              FStar_Tactics_Printing.goal_to_string_verbose goal in
            FStar_Util.format1 "Goal %s is already solved" uu____1244 in
          FStar_Tactics_Monad.fail uu____1243
      | FStar_Pervasives_Native.None ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           FStar_Tactics_Monad.ret ())
let (trysolve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1260 = FStar_Tactics_Types.goal_env goal in
      let uu____1261 = FStar_Tactics_Types.goal_witness goal in
      do_unify uu____1260 solution uu____1261
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      FStar_Tactics_Monad.mlog
        (fun uu____1280 ->
           let uu____1281 =
             let uu____1282 = FStar_Tactics_Types.goal_witness goal in
             FStar_Syntax_Print.term_to_string uu____1282 in
           let uu____1283 = FStar_Syntax_Print.term_to_string solution in
           FStar_Util.print2 "solve %s := %s\n" uu____1281 uu____1283)
        (fun uu____1286 ->
           let uu____1287 = trysolve goal solution in
           FStar_Tactics_Monad.bind uu____1287
             (fun b ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____1295 ->
                       FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu____1297 =
                     let uu____1298 =
                       let uu____1299 = FStar_Tactics_Types.goal_env goal in
                       tts uu____1299 solution in
                     let uu____1300 =
                       let uu____1301 = FStar_Tactics_Types.goal_env goal in
                       let uu____1302 = FStar_Tactics_Types.goal_witness goal in
                       tts uu____1301 uu____1302 in
                     let uu____1303 =
                       let uu____1304 = FStar_Tactics_Types.goal_env goal in
                       let uu____1305 = FStar_Tactics_Types.goal_type goal in
                       tts uu____1304 uu____1305 in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1298 uu____1300 uu____1303 in
                   FStar_Tactics_Monad.fail uu____1297)))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1320 = set_solution goal solution in
      FStar_Tactics_Monad.bind uu____1320
        (fun uu____1324 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu____1326 -> FStar_Tactics_Monad.remove_solved_goals))
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1333 = FStar_Syntax_Util.un_squash t1 in
    match uu____1333 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu____1344 =
          let uu____1345 = FStar_Syntax_Subst.compress t'1 in
          uu____1345.FStar_Syntax_Syntax.n in
        (match uu____1344 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1349 -> false)
    | uu____1350 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1360 = FStar_Syntax_Util.un_squash t in
    match uu____1360 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1370 =
          let uu____1371 = FStar_Syntax_Subst.compress t' in
          uu____1371.FStar_Syntax_Syntax.n in
        (match uu____1370 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1375 -> false)
    | uu____1376 -> false
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____1390 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                (let uu____1399 =
                   let uu____1400 = FStar_Tactics_Types.goal_type g in
                   uu____1400.FStar_Syntax_Syntax.pos in
                 let uu____1403 =
                   let uu____1408 =
                     let uu____1409 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1409 in
                   (FStar_Errors.Warning_TacAdmit, uu____1408) in
                 FStar_Errors.log_issue uu____1399 uu____1403);
                solve' g t)) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tadmit_t") uu____1390
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1424 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStar_Tactics_Types.freshness in
         let ps1 =
           let uu___291_1434 = ps in
           {
             FStar_Tactics_Types.main_context =
               (uu___291_1434.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___291_1434.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___291_1434.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___291_1434.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___291_1434.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___291_1434.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___291_1434.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___291_1434.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___291_1434.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___291_1434.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___291_1434.FStar_Tactics_Types.local_state)
           } in
         let uu____1435 = FStar_Tactics_Monad.set ps1 in
         FStar_Tactics_Monad.bind uu____1435
           (fun uu____1440 ->
              let uu____1441 = FStar_BigInt.of_int_fs n in
              FStar_Tactics_Monad.ret uu____1441))
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1448 ->
    let uu____1451 =
      let uu____1452 = FStar_Util.now_ms () in
      FStar_All.pipe_right uu____1452 FStar_BigInt.of_int_fs in
    FStar_Tactics_Monad.ret uu____1451
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1495 ->
                let uu____1496 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1496)
             (fun uu____1499 ->
                let e1 =
                  let uu___300_1501 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___300_1501.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___300_1501.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___300_1501.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___300_1501.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___300_1501.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___300_1501.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___300_1501.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___300_1501.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___300_1501.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___300_1501.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___300_1501.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___300_1501.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___300_1501.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___300_1501.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___300_1501.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___300_1501.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___300_1501.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___300_1501.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___300_1501.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___300_1501.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___300_1501.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___300_1501.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___300_1501.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___300_1501.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___300_1501.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___300_1501.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___300_1501.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___300_1501.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___300_1501.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___300_1501.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___300_1501.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___300_1501.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___300_1501.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___300_1501.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___300_1501.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___300_1501.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___300_1501.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___300_1501.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___300_1501.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___300_1501.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___300_1501.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___300_1501.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___300_1501.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___300_1501.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___300_1501.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___300_1501.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___304_1512 ->
                     match () with
                     | () ->
                         let uu____1521 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t in
                         FStar_Tactics_Monad.ret uu____1521) ()
                with
                | FStar_Errors.Err (uu____1548, msg) ->
                    let uu____1550 = tts e1 t in
                    let uu____1551 =
                      let uu____1552 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1552
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1550 uu____1551 msg
                | FStar_Errors.Error (uu____1559, msg, uu____1561) ->
                    let uu____1562 = tts e1 t in
                    let uu____1563 =
                      let uu____1564 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1564
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1562 uu____1563 msg))
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1613 ->
                let uu____1614 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____1614)
             (fun uu____1617 ->
                let e1 =
                  let uu___321_1619 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___321_1619.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___321_1619.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___321_1619.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___321_1619.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___321_1619.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___321_1619.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___321_1619.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___321_1619.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___321_1619.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___321_1619.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___321_1619.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___321_1619.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___321_1619.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___321_1619.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___321_1619.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___321_1619.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___321_1619.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___321_1619.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___321_1619.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___321_1619.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___321_1619.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___321_1619.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___321_1619.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___321_1619.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___321_1619.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___321_1619.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___321_1619.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___321_1619.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___321_1619.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___321_1619.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___321_1619.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___321_1619.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___321_1619.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___321_1619.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___321_1619.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___321_1619.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___321_1619.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___321_1619.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___321_1619.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___321_1619.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___321_1619.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___321_1619.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___321_1619.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___321_1619.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___321_1619.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___321_1619.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___325_1633 ->
                     match () with
                     | () ->
                         let uu____1642 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t in
                         (match uu____1642 with
                          | (t1, lc, g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____1680, msg) ->
                    let uu____1682 = tts e1 t in
                    let uu____1683 =
                      let uu____1684 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1684
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1682 uu____1683 msg
                | FStar_Errors.Error (uu____1691, msg, uu____1693) ->
                    let uu____1694 = tts e1 t in
                    let uu____1695 =
                      let uu____1696 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1696
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1694 uu____1695 msg))
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1745 ->
                let uu____1746 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____1746)
             (fun uu____1750 ->
                let e1 =
                  let uu___346_1752 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___346_1752.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___346_1752.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___346_1752.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___346_1752.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___346_1752.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___346_1752.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___346_1752.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___346_1752.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___346_1752.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___346_1752.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___346_1752.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___346_1752.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___346_1752.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___346_1752.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___346_1752.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___346_1752.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___346_1752.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___346_1752.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___346_1752.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___346_1752.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___346_1752.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___346_1752.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___346_1752.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___346_1752.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___346_1752.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___346_1752.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___346_1752.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___346_1752.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___346_1752.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___346_1752.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___346_1752.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___346_1752.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___346_1752.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___346_1752.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___346_1752.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___346_1752.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___346_1752.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___346_1752.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___346_1752.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___346_1752.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___346_1752.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___346_1752.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___346_1752.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___346_1752.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___346_1752.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___346_1752.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                let e2 =
                  let uu___349_1754 = e1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___349_1754.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___349_1754.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___349_1754.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___349_1754.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___349_1754.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___349_1754.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___349_1754.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___349_1754.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___349_1754.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___349_1754.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___349_1754.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___349_1754.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___349_1754.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___349_1754.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___349_1754.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___349_1754.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___349_1754.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___349_1754.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___349_1754.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___349_1754.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___349_1754.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___349_1754.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___349_1754.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___349_1754.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___349_1754.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___349_1754.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___349_1754.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___349_1754.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___349_1754.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___349_1754.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___349_1754.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___349_1754.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___349_1754.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___349_1754.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___349_1754.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___349_1754.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___349_1754.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___349_1754.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___349_1754.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___349_1754.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___349_1754.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___349_1754.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___349_1754.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___349_1754.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___349_1754.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___349_1754.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___353_1765 ->
                     match () with
                     | () ->
                         let uu____1774 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t in
                         FStar_Tactics_Monad.ret uu____1774) ()
                with
                | FStar_Errors.Err (uu____1801, msg) ->
                    let uu____1803 = tts e2 t in
                    let uu____1804 =
                      let uu____1805 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1805
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1803 uu____1804 msg
                | FStar_Errors.Error (uu____1812, msg, uu____1814) ->
                    let uu____1815 = tts e2 t in
                    let uu____1816 =
                      let uu____1817 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1817
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1815 uu____1816 msg))
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta] in
      let t1 = normalize steps e t in is_true t1
let (get_guard_policy :
  unit -> FStar_Tactics_Types.guard_policy FStar_Tactics_Monad.tac) =
  fun uu____1844 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Tactics_Monad.set
           (let uu___374_1862 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___374_1862.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___374_1862.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___374_1862.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___374_1862.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___374_1862.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___374_1862.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___374_1862.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___374_1862.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___374_1862.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___374_1862.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___374_1862.FStar_Tactics_Types.local_state)
            }))
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu____1886 = get_guard_policy () in
      FStar_Tactics_Monad.bind uu____1886
        (fun old_pol ->
           let uu____1892 = set_guard_policy pol in
           FStar_Tactics_Monad.bind uu____1892
             (fun uu____1896 ->
                FStar_Tactics_Monad.bind t
                  (fun r ->
                     let uu____1900 = set_guard_policy old_pol in
                     FStar_Tactics_Monad.bind uu____1900
                       (fun uu____1904 -> FStar_Tactics_Monad.ret r))))
let (getopts : FStar_Options.optionstate FStar_Tactics_Monad.tac) =
  let uu____1907 = trytac FStar_Tactics_Monad.cur_goal in
  FStar_Tactics_Monad.bind uu____1907
    (fun uu___0_1916 ->
       match uu___0_1916 with
       | FStar_Pervasives_Native.Some g ->
           FStar_Tactics_Monad.ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu____1922 = FStar_Options.peek () in
           FStar_Tactics_Monad.ret uu____1922)
let (proc_guard :
  Prims.string ->
    env -> FStar_TypeChecker_Common.guard_t -> unit FStar_Tactics_Monad.tac)
  =
  fun reason ->
    fun e ->
      fun g ->
        FStar_Tactics_Monad.mlog
          (fun uu____1944 ->
             let uu____1945 = FStar_TypeChecker_Rel.guard_to_string e g in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____1945)
          (fun uu____1948 ->
             let uu____1949 =
               FStar_Tactics_Monad.add_implicits
                 g.FStar_TypeChecker_Common.implicits in
             FStar_Tactics_Monad.bind uu____1949
               (fun uu____1953 ->
                  FStar_Tactics_Monad.bind getopts
                    (fun opts ->
                       let uu____1957 =
                         let uu____1958 =
                           FStar_TypeChecker_Rel.simplify_guard e g in
                         uu____1958.FStar_TypeChecker_Common.guard_f in
                       match uu____1957 with
                       | FStar_TypeChecker_Common.Trivial ->
                           FStar_Tactics_Monad.ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____1962 = istrivial e f in
                           if uu____1962
                           then FStar_Tactics_Monad.ret ()
                           else
                             FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                               (fun ps ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop ->
                                      ((let uu____1972 =
                                          let uu____1977 =
                                            let uu____1978 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____1978 in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____1977) in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____1972);
                                       FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Goal ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1981 ->
                                           let uu____1982 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____1982)
                                        (fun uu____1985 ->
                                           let uu____1986 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____1986
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___403_1993 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___403_1993.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___403_1993.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___403_1993.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___403_1993.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.SMT ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____1996 ->
                                           let uu____1997 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____1997)
                                        (fun uu____2000 ->
                                           let uu____2001 =
                                             FStar_Tactics_Monad.mk_irrelevant_goal
                                               reason e f opts "" in
                                           FStar_Tactics_Monad.bind
                                             uu____2001
                                             (fun goal ->
                                                let goal1 =
                                                  let uu___410_2008 = goal in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___410_2008.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___410_2008.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___410_2008.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___410_2008.FStar_Tactics_Types.label)
                                                  } in
                                                FStar_Tactics_Monad.push_smt_goals
                                                  [goal1]))
                                  | FStar_Tactics_Types.Force ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____2011 ->
                                           let uu____2012 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2012)
                                        (fun uu____2014 ->
                                           try
                                             (fun uu___417_2019 ->
                                                match () with
                                                | () ->
                                                    let uu____2022 =
                                                      let uu____2023 =
                                                        let uu____2024 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2024 in
                                                      Prims.op_Negation
                                                        uu____2023 in
                                                    if uu____2022
                                                    then
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu____2029 ->
                                                           let uu____2030 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2030)
                                                        (fun uu____2032 ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else
                                                      FStar_Tactics_Monad.ret
                                                        ()) ()
                                           with
                                           | uu___416_2035 ->
                                               FStar_Tactics_Monad.mlog
                                                 (fun uu____2040 ->
                                                    let uu____2041 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2041)
                                                 (fun uu____2043 ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
let (tcc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____2058 =
        let uu____2061 = __tc_lax e t in
        FStar_Tactics_Monad.bind uu____2061
          (fun uu____2081 ->
             match uu____2081 with
             | (uu____2090, lc, uu____2092) ->
                 let uu____2093 =
                   let uu____2094 = FStar_TypeChecker_Common.lcomp_comp lc in
                   FStar_All.pipe_right uu____2094
                     FStar_Pervasives_Native.fst in
                 FStar_Tactics_Monad.ret uu____2093) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tcc") uu____2058
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____2121 =
        let uu____2126 = tcc e t in
        FStar_Tactics_Monad.bind uu____2126
          (fun c -> FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tc") uu____2121
let (trivial : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____2149 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____2155 =
           let uu____2156 = FStar_Tactics_Types.goal_env goal in
           let uu____2157 = FStar_Tactics_Types.goal_type goal in
           istrivial uu____2156 uu____2157 in
         if uu____2155
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2161 =
              let uu____2162 = FStar_Tactics_Types.goal_env goal in
              let uu____2163 = FStar_Tactics_Types.goal_type goal in
              tts uu____2162 uu____2163 in
            fail1 "Not a trivial goal: %s" uu____2161))
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a FStar_Tactics_Monad.tac ->
        'b FStar_Tactics_Monad.tac -> ('a * 'b) FStar_Tactics_Monad.tac
  =
  fun n ->
    fun l ->
      fun r ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun p ->
             let uu____2212 =
               try
                 (fun uu___468_2235 ->
                    match () with
                    | () ->
                        let uu____2246 =
                          let uu____2255 = FStar_BigInt.to_int_fs n in
                          FStar_List.splitAt uu____2255
                            p.FStar_Tactics_Types.goals in
                        FStar_Tactics_Monad.ret uu____2246) ()
               with
               | uu___467_2265 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals" in
             FStar_Tactics_Monad.bind uu____2212
               (fun uu____2301 ->
                  match uu____2301 with
                  | (lgs, rgs) ->
                      let lp =
                        let uu___450_2327 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___450_2327.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___450_2327.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___450_2327.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___450_2327.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___450_2327.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___450_2327.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___450_2327.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___450_2327.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___450_2327.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___450_2327.FStar_Tactics_Types.local_state)
                        } in
                      let uu____2328 = FStar_Tactics_Monad.set lp in
                      FStar_Tactics_Monad.bind uu____2328
                        (fun uu____2336 ->
                           FStar_Tactics_Monad.bind l
                             (fun a1 ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       let uu___456_2352 = lp' in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___456_2352.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___456_2352.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___456_2352.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___456_2352.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___456_2352.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___456_2352.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___456_2352.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___456_2352.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___456_2352.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___456_2352.FStar_Tactics_Types.local_state)
                                       } in
                                     let uu____2353 =
                                       FStar_Tactics_Monad.set rp in
                                     FStar_Tactics_Monad.bind uu____2353
                                       (fun uu____2361 ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b1 ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      let uu___462_2377 = rp' in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_List.append
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___462_2377.FStar_Tactics_Types.local_state)
                                                      } in
                                                    let uu____2378 =
                                                      FStar_Tactics_Monad.set
                                                        p' in
                                                    FStar_Tactics_Monad.bind
                                                      uu____2378
                                                      (fun uu____2386 ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu____2392 ->
                                                              FStar_Tactics_Monad.ret
                                                                (a1, b1)))))))))))
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f ->
    let uu____2413 = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac in
    FStar_Tactics_Monad.bind uu____2413
      (fun uu____2426 ->
         match uu____2426 with | (a1, ()) -> FStar_Tactics_Monad.ret a1)
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu____2463::uu____2464 ->
             let uu____2467 =
               let uu____2476 = map tau in
               divide FStar_BigInt.one tau uu____2476 in
             FStar_Tactics_Monad.bind uu____2467
               (fun uu____2494 ->
                  match uu____2494 with
                  | (h, t) -> FStar_Tactics_Monad.ret (h :: t)))
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu____2535 =
        FStar_Tactics_Monad.bind t1
          (fun uu____2540 ->
             let uu____2541 = map t2 in
             FStar_Tactics_Monad.bind uu____2541
               (fun uu____2549 -> FStar_Tactics_Monad.ret ())) in
      focus uu____2535
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu____2558 ->
    let uu____2561 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____2570 =
             let uu____2577 =
               let uu____2578 = FStar_Tactics_Types.goal_env goal in
               let uu____2579 = FStar_Tactics_Types.goal_type goal in
               whnf uu____2578 uu____2579 in
             FStar_Syntax_Util.arrow_one uu____2577 in
           match uu____2570 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____2588 =
                 let uu____2589 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu____2589 in
               if uu____2588
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2594 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.push_binders uu____2594 [b] in
                  let typ' = FStar_Syntax_Util.comp_result c in
                  let uu____2610 =
                    FStar_Tactics_Monad.new_uvar "intro" env' typ' in
                  FStar_Tactics_Monad.bind uu____2610
                    (fun uu____2626 ->
                       match uu____2626 with
                       | (body, ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)) in
                           let uu____2650 = set_solution goal sol in
                           FStar_Tactics_Monad.bind uu____2650
                             (fun uu____2656 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu____2658 =
                                  let uu____2661 = bnorm_goal g in
                                  FStar_Tactics_Monad.replace_cur uu____2661 in
                                FStar_Tactics_Monad.bind uu____2658
                                  (fun uu____2663 ->
                                     FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None ->
               let uu____2668 =
                 let uu____2669 = FStar_Tactics_Types.goal_env goal in
                 let uu____2670 = FStar_Tactics_Types.goal_type goal in
                 tts uu____2669 uu____2670 in
               fail1 "goal is not an arrow (%s)" uu____2668) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "intro") uu____2561
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu____2685 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2706 =
            let uu____2713 =
              let uu____2714 = FStar_Tactics_Types.goal_env goal in
              let uu____2715 = FStar_Tactics_Types.goal_type goal in
              whnf uu____2714 uu____2715 in
            FStar_Syntax_Util.arrow_one uu____2713 in
          match uu____2706 with
          | FStar_Pervasives_Native.Some (b, c) ->
              let uu____2728 =
                let uu____2729 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu____2729 in
              if uu____2728
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu____2742 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____2742 in
                 let bs =
                   let uu____2752 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2752; b] in
                 let env' =
                   let uu____2778 = FStar_Tactics_Types.goal_env goal in
                   FStar_TypeChecker_Env.push_binders uu____2778 bs in
                 let uu____2779 =
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) in
                 FStar_Tactics_Monad.bind uu____2779
                   (fun uu____2804 ->
                      match uu____2804 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu____2818 =
                              FStar_Tactics_Types.goal_type goal in
                            let uu____2821 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____2818
                              FStar_Parser_Const.effect_Tot_lid uu____2821 []
                              FStar_Range.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu____2839 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu____2839 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu____2861 =
                                   let uu____2862 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu____2862.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1)) uu____2861 in
                               let uu____2875 = set_solution goal tm in
                               FStar_Tactics_Monad.bind uu____2875
                                 (fun uu____2884 ->
                                    let uu____2885 =
                                      let uu____2888 =
                                        bnorm_goal
                                          (let uu___533_2891 = goal in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___533_2891.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___533_2891.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___533_2891.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___533_2891.FStar_Tactics_Types.label)
                                           }) in
                                      FStar_Tactics_Monad.replace_cur
                                        uu____2888 in
                                    FStar_Tactics_Monad.bind uu____2885
                                      (fun uu____2898 ->
                                         let uu____2899 =
                                           let uu____2904 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu____2904, b) in
                                         FStar_Tactics_Monad.ret uu____2899)))))
          | FStar_Pervasives_Native.None ->
              let uu____2913 =
                let uu____2914 = FStar_Tactics_Types.goal_env goal in
                let uu____2915 = FStar_Tactics_Types.goal_type goal in
                tts uu____2914 uu____2915 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2913))
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____2937 ->
              let uu____2938 =
                let uu____2939 = FStar_Tactics_Types.goal_witness goal in
                FStar_Syntax_Print.term_to_string uu____2939 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2938)
           (fun uu____2944 ->
              let steps =
                let uu____2948 = FStar_TypeChecker_Normalize.tr_norm_steps s in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____2948 in
              let t =
                let uu____2952 = FStar_Tactics_Types.goal_env goal in
                let uu____2953 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu____2952 uu____2953 in
              let uu____2954 = FStar_Tactics_Types.goal_with_type goal t in
              FStar_Tactics_Monad.replace_cur uu____2954))
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu____2978 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____2986 -> g.FStar_Tactics_Types.opts
                 | uu____2989 -> FStar_Options.peek () in
               FStar_Tactics_Monad.mlog
                 (fun uu____2994 ->
                    let uu____2995 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____2995)
                 (fun uu____2998 ->
                    let uu____2999 = __tc_lax e t in
                    FStar_Tactics_Monad.bind uu____2999
                      (fun uu____3020 ->
                         match uu____3020 with
                         | (t1, uu____3030, uu____3031) ->
                             let steps =
                               let uu____3035 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____3035 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             FStar_Tactics_Monad.mlog
                               (fun uu____3041 ->
                                  let uu____3042 =
                                    FStar_Syntax_Print.term_to_string t2 in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____3042)
                               (fun uu____3044 -> FStar_Tactics_Monad.ret t2)))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_term")
          uu____2978
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____3055 ->
    let uu____3058 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____3065 =
             let uu____3076 = FStar_Tactics_Types.goal_env g in
             let uu____3077 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu____3076 uu____3077 in
           match uu____3065 with
           | (uu____3080, FStar_Pervasives_Native.None) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t in
               let uu____3105 =
                 let uu____3110 =
                   let uu____3115 =
                     let uu____3116 = FStar_Syntax_Syntax.mk_binder bv in
                     [uu____3116] in
                   FStar_Syntax_Subst.open_term uu____3115 phi in
                 match uu____3110 with
                 | (bvs, phi1) ->
                     let uu____3141 =
                       let uu____3142 = FStar_List.hd bvs in
                       FStar_Pervasives_Native.fst uu____3142 in
                     (uu____3141, phi1) in
               (match uu____3105 with
                | (bv1, phi1) ->
                    let uu____3161 =
                      let uu____3164 = FStar_Tactics_Types.goal_env g in
                      let uu____3165 =
                        let uu____3166 =
                          let uu____3169 =
                            let uu____3170 =
                              let uu____3177 =
                                FStar_Tactics_Types.goal_witness g in
                              (bv1, uu____3177) in
                            FStar_Syntax_Syntax.NT uu____3170 in
                          [uu____3169] in
                        FStar_Syntax_Subst.subst uu____3166 phi1 in
                      FStar_Tactics_Monad.mk_irrelevant_goal
                        "refine_intro refinement" uu____3164 uu____3165
                        g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label in
                    FStar_Tactics_Monad.bind uu____3161
                      (fun g2 ->
                         FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                           (fun uu____3185 ->
                              FStar_Tactics_Monad.add_goals [g1; g2])))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "refine_intro")
      uu____3058
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let env1 =
             if set_expected_typ
             then
               let uu____3209 = FStar_Tactics_Types.goal_env goal in
               let uu____3210 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu____3209 uu____3210
             else FStar_Tactics_Types.goal_env goal in
           let uu____3212 = __tc env1 t in
           FStar_Tactics_Monad.bind uu____3212
             (fun uu____3231 ->
                match uu____3231 with
                | (t1, typ, guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu____3246 ->
                         let uu____3247 =
                           FStar_Syntax_Print.term_to_string typ in
                         let uu____3248 =
                           let uu____3249 = FStar_Tactics_Types.goal_env goal in
                           FStar_TypeChecker_Rel.guard_to_string uu____3249
                             guard in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3247 uu____3248)
                      (fun uu____3252 ->
                         let uu____3253 =
                           let uu____3256 = FStar_Tactics_Types.goal_env goal in
                           proc_guard "__exact typing" uu____3256 guard in
                         FStar_Tactics_Monad.bind uu____3253
                           (fun uu____3258 ->
                              FStar_Tactics_Monad.mlog
                                (fun uu____3262 ->
                                   let uu____3263 =
                                     FStar_Syntax_Print.term_to_string typ in
                                   let uu____3264 =
                                     let uu____3265 =
                                       FStar_Tactics_Types.goal_type goal in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3265 in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3263 uu____3264)
                                (fun uu____3268 ->
                                   let uu____3269 =
                                     let uu____3272 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu____3273 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify uu____3272 typ uu____3273 in
                                   FStar_Tactics_Monad.bind uu____3269
                                     (fun b ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3279 =
                                             let uu____3284 =
                                               let uu____3289 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal in
                                               tts uu____3289 in
                                             let uu____3290 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____3284 typ uu____3290 in
                                           match uu____3279 with
                                           | (typ1, goalt) ->
                                               let uu____3295 =
                                                 let uu____3296 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 tts uu____3296 t1 in
                                               let uu____3297 =
                                                 let uu____3298 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 let uu____3299 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal in
                                                 tts uu____3298 uu____3299 in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____3295 typ1 goalt
                                                 uu____3297)))))))
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu____3319 =
          FStar_Tactics_Monad.mlog
            (fun uu____3324 ->
               let uu____3325 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3325)
            (fun uu____3328 ->
               let uu____3329 =
                 let uu____3336 = __exact_now set_expected_typ tm in
                 catch uu____3336 in
               FStar_Tactics_Monad.bind uu____3329
                 (fun uu___2_3345 ->
                    match uu___2_3345 with
                    | FStar_Util.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Util.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu____3356 ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3359 ->
                             let uu____3360 =
                               let uu____3367 =
                                 let uu____3370 =
                                   norm [FStar_Syntax_Embeddings.Delta] in
                                 FStar_Tactics_Monad.bind uu____3370
                                   (fun uu____3375 ->
                                      let uu____3376 = refine_intro () in
                                      FStar_Tactics_Monad.bind uu____3376
                                        (fun uu____3380 ->
                                           __exact_now set_expected_typ tm)) in
                               catch uu____3367 in
                             FStar_Tactics_Monad.bind uu____3360
                               (fun uu___1_3387 ->
                                  match uu___1_3387 with
                                  | FStar_Util.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3396 ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____3398 ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Util.Inl uu____3399 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3401 ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____3403 ->
                                           FStar_Tactics_Monad.traise e))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "exact") uu____3319
let rec (__try_unify_by_application :
  Prims.bool ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
              FStar_Syntax_Syntax.ctx_uvar) Prims.list
              FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun acc ->
      fun e ->
        fun ty1 ->
          fun ty2 ->
            let f = if only_match then do_match else do_unify in
            let uu____3496 = f e ty2 ty1 in
            FStar_Tactics_Monad.bind uu____3496
              (fun uu___3_3508 ->
                 if uu___3_3508
                 then FStar_Tactics_Monad.ret acc
                 else
                   (let uu____3527 = FStar_Syntax_Util.arrow_one ty1 in
                    match uu____3527 with
                    | FStar_Pervasives_Native.None ->
                        let uu____3548 = term_to_string e ty1 in
                        let uu____3549 = term_to_string e ty2 in
                        fail2 "Could not instantiate, %s to %s" uu____3548
                          uu____3549
                    | FStar_Pervasives_Native.Some (b, c) ->
                        let uu____3564 =
                          let uu____3565 = FStar_Syntax_Util.is_total_comp c in
                          Prims.op_Negation uu____3565 in
                        if uu____3564
                        then FStar_Tactics_Monad.fail "Codomain is effectful"
                        else
                          (let uu____3585 =
                             FStar_Tactics_Monad.new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           FStar_Tactics_Monad.bind uu____3585
                             (fun uu____3609 ->
                                match uu____3609 with
                                | (uvt, uv) ->
                                    FStar_Tactics_Monad.mlog
                                      (fun uu____3636 ->
                                         let uu____3637 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             uv in
                                         FStar_Util.print1
                                           "t_apply: generated uvar %s\n"
                                           uu____3637)
                                      (fun uu____3641 ->
                                         let typ =
                                           FStar_Syntax_Util.comp_result c in
                                         let typ' =
                                           FStar_Syntax_Subst.subst
                                             [FStar_Syntax_Syntax.NT
                                                ((FStar_Pervasives_Native.fst
                                                    b), uvt)] typ in
                                         __try_unify_by_application
                                           only_match
                                           ((uvt,
                                              (FStar_Pervasives_Native.snd b),
                                              uv) :: acc) e typ' ty2)))))
let (try_unify_by_application :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun e ->
      fun ty1 ->
        fun ty2 -> __try_unify_by_application only_match [] e ty1 ty2
let (t_apply :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun uopt ->
    fun only_match ->
      fun tm ->
        let uu____3723 =
          FStar_Tactics_Monad.mlog
            (fun uu____3728 ->
               let uu____3729 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____3729)
            (fun uu____3731 ->
               FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                 (fun goal ->
                    let e = FStar_Tactics_Types.goal_env goal in
                    FStar_Tactics_Monad.mlog
                      (fun uu____3740 ->
                         let uu____3741 =
                           FStar_Syntax_Print.term_to_string tm in
                         let uu____3742 =
                           FStar_Tactics_Printing.goal_to_string_verbose goal in
                         let uu____3743 =
                           FStar_TypeChecker_Env.print_gamma
                             e.FStar_TypeChecker_Env.gamma in
                         FStar_Util.print3
                           "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
                           uu____3741 uu____3742 uu____3743)
                      (fun uu____3746 ->
                         let uu____3747 = __tc e tm in
                         FStar_Tactics_Monad.bind uu____3747
                           (fun uu____3768 ->
                              match uu____3768 with
                              | (tm1, typ, guard) ->
                                  let typ1 = bnorm e typ in
                                  let uu____3781 =
                                    let uu____3792 =
                                      FStar_Tactics_Types.goal_type goal in
                                    try_unify_by_application only_match e
                                      typ1 uu____3792 in
                                  FStar_Tactics_Monad.bind uu____3781
                                    (fun uvs ->
                                       FStar_Tactics_Monad.mlog
                                         (fun uu____3813 ->
                                            let uu____3814 =
                                              FStar_Common.string_of_list
                                                (fun uu____3825 ->
                                                   match uu____3825 with
                                                   | (t, uu____3833,
                                                      uu____3834) ->
                                                       FStar_Syntax_Print.term_to_string
                                                         t) uvs in
                                            FStar_Util.print1
                                              "t_apply: found args = %s\n"
                                              uu____3814)
                                         (fun uu____3841 ->
                                            let fix_qual q =
                                              match q with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.Meta
                                                  uu____3856) ->
                                                  FStar_Pervasives_Native.Some
                                                    (FStar_Syntax_Syntax.Implicit
                                                       false)
                                              | uu____3857 -> q in
                                            let w =
                                              FStar_List.fold_right
                                                (fun uu____3880 ->
                                                   fun w ->
                                                     match uu____3880 with
                                                     | (uvt, q, uu____3898)
                                                         ->
                                                         FStar_Syntax_Util.mk_app
                                                           w
                                                           [(uvt,
                                                              (fix_qual q))])
                                                uvs tm1 in
                                            let uvset =
                                              let uu____3930 =
                                                FStar_Syntax_Free.new_uv_set
                                                  () in
                                              FStar_List.fold_right
                                                (fun uu____3947 ->
                                                   fun s ->
                                                     match uu____3947 with
                                                     | (uu____3959,
                                                        uu____3960, uv) ->
                                                         let uu____3962 =
                                                           FStar_Syntax_Free.uvars
                                                             uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                         FStar_Util.set_union
                                                           s uu____3962) uvs
                                                uu____3930 in
                                            let free_in_some_goal uv =
                                              FStar_Util.set_mem uv uvset in
                                            let uu____3971 = solve' goal w in
                                            FStar_Tactics_Monad.bind
                                              uu____3971
                                              (fun uu____3976 ->
                                                 let uu____3977 =
                                                   FStar_Tactics_Monad.mapM
                                                     (fun uu____3994 ->
                                                        match uu____3994 with
                                                        | (uvt, q, uv) ->
                                                            let uu____4006 =
                                                              FStar_Syntax_Unionfind.find
                                                                uv.FStar_Syntax_Syntax.ctx_uvar_head in
                                                            (match uu____4006
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 uu____4011
                                                                 ->
                                                                 FStar_Tactics_Monad.ret
                                                                   ()
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 let uu____4012
                                                                   =
                                                                   uopt &&
                                                                    (free_in_some_goal
                                                                    uv) in
                                                                 if
                                                                   uu____4012
                                                                 then
                                                                   FStar_Tactics_Monad.ret
                                                                    ()
                                                                 else
                                                                   (let uu____4016
                                                                    =
                                                                    let uu____4019
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___696_4022
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___696_4022.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___696_4022.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___696_4022.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    [uu____4019] in
                                                                    FStar_Tactics_Monad.add_goals
                                                                    uu____4016)))
                                                     uvs in
                                                 FStar_Tactics_Monad.bind
                                                   uu____3977
                                                   (fun uu____4026 ->
                                                      proc_guard
                                                        "apply guard" e guard)))))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply") uu____3723
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c in
    let uu____4051 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid in
    if uu____4051
    then
      let uu____4058 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4073 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4126 -> failwith "apply_lemma: impossible: not a lemma" in
      match uu____4058 with
      | (pre, post) ->
          let post1 =
            let uu____4158 =
              let uu____4169 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____4169] in
            FStar_Syntax_Util.mk_app post uu____4158 in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4199 =
         (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
           ||
           (FStar_Syntax_Util.is_ghost_effect
              ct.FStar_Syntax_Syntax.effect_name) in
       if uu____4199
       then
         let uu____4206 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ in
         FStar_Util.map_opt uu____4206
           (fun post -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
let rec fold_left :
  'a 'b .
    ('a -> 'b -> 'b FStar_Tactics_Monad.tac) ->
      'b -> 'a Prims.list -> 'b FStar_Tactics_Monad.tac
  =
  fun f ->
    fun e ->
      fun xs ->
        match xs with
        | [] -> FStar_Tactics_Monad.ret e
        | x::xs1 ->
            let uu____4283 = f x e in
            FStar_Tactics_Monad.bind uu____4283
              (fun e' -> fold_left f e' xs1)
let (t_apply_lemma :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun noinst ->
    fun noinst_lhs ->
      fun tm ->
        let uu____4307 =
          let uu____4310 =
            FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
              (fun ps ->
                 FStar_Tactics_Monad.mlog
                   (fun uu____4317 ->
                      let uu____4318 = FStar_Syntax_Print.term_to_string tm in
                      FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4318)
                   (fun uu____4321 ->
                      let is_unit_t t =
                        let uu____4328 =
                          let uu____4329 = FStar_Syntax_Subst.compress t in
                          uu____4329.FStar_Syntax_Syntax.n in
                        match uu____4328 with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.unit_lid
                            -> true
                        | uu____4333 -> false in
                      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                        (fun goal ->
                           let env1 = FStar_Tactics_Types.goal_env goal in
                           let uu____4339 = __tc env1 tm in
                           FStar_Tactics_Monad.bind uu____4339
                             (fun uu____4362 ->
                                match uu____4362 with
                                | (tm1, t, guard) ->
                                    let uu____4374 =
                                      FStar_Syntax_Util.arrow_formals_comp t in
                                    (match uu____4374 with
                                     | (bs, comp) ->
                                         let uu____4383 = lemma_or_sq comp in
                                         (match uu____4383 with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Tactics_Monad.fail
                                                "not a lemma or squashed function"
                                          | FStar_Pervasives_Native.Some
                                              (pre, post) ->
                                              let uu____4402 =
                                                fold_left
                                                  (fun uu____4464 ->
                                                     fun uu____4465 ->
                                                       match (uu____4464,
                                                               uu____4465)
                                                       with
                                                       | ((b, aq),
                                                          (uvs, imps, subst))
                                                           ->
                                                           let b_t =
                                                             FStar_Syntax_Subst.subst
                                                               subst
                                                               b.FStar_Syntax_Syntax.sort in
                                                           let uu____4616 =
                                                             is_unit_t b_t in
                                                           if uu____4616
                                                           then
                                                             FStar_All.pipe_left
                                                               FStar_Tactics_Monad.ret
                                                               (((FStar_Syntax_Util.exp_unit,
                                                                   aq) ::
                                                                 uvs), imps,
                                                                 ((FStar_Syntax_Syntax.NT
                                                                    (b,
                                                                    FStar_Syntax_Util.exp_unit))
                                                                 :: subst))
                                                           else
                                                             (let uu____4736
                                                                =
                                                                FStar_Tactics_Monad.new_uvar
                                                                  "apply_lemma"
                                                                  env1 b_t in
                                                              FStar_Tactics_Monad.bind
                                                                uu____4736
                                                                (fun
                                                                   uu____4772
                                                                   ->
                                                                   match uu____4772
                                                                   with
                                                                   | 
                                                                   (t1, u) ->
                                                                    FStar_All.pipe_left
                                                                    FStar_Tactics_Monad.ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst)))))
                                                  ([], [], []) bs in
                                              FStar_Tactics_Monad.bind
                                                uu____4402
                                                (fun uu____4960 ->
                                                   match uu____4960 with
                                                   | (uvs, implicits1, subst)
                                                       ->
                                                       let implicits2 =
                                                         FStar_List.rev
                                                           implicits1 in
                                                       let uvs1 =
                                                         FStar_List.rev uvs in
                                                       let pre1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst pre in
                                                       let post1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst post in
                                                       let post_u =
                                                         env1.FStar_TypeChecker_Env.universe_of
                                                           env1 post1 in
                                                       let cmp_func =
                                                         if noinst
                                                         then do_match
                                                         else
                                                           if noinst_lhs
                                                           then
                                                             do_match_on_lhs
                                                           else do_unify in
                                                       let uu____5088 =
                                                         let uu____5091 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal in
                                                         let uu____5092 =
                                                           FStar_Syntax_Util.mk_squash
                                                             post_u post1 in
                                                         cmp_func env1
                                                           uu____5091
                                                           uu____5092 in
                                                       FStar_Tactics_Monad.bind
                                                         uu____5088
                                                         (fun b ->
                                                            if
                                                              Prims.op_Negation
                                                                b
                                                            then
                                                              let uu____5101
                                                                =
                                                                let uu____5106
                                                                  =
                                                                  FStar_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                let uu____5107
                                                                  =
                                                                  FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                FStar_TypeChecker_Err.print_discrepancy
                                                                  (tts env1)
                                                                  uu____5106
                                                                  uu____5107 in
                                                              match uu____5101
                                                              with
                                                              | (post2,
                                                                 goalt) ->
                                                                  let uu____5112
                                                                    =
                                                                    tts env1
                                                                    tm1 in
                                                                  fail3
                                                                    "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                    uu____5112
                                                                    post2
                                                                    goalt
                                                            else
                                                              (let uu____5114
                                                                 =
                                                                 solve' goal
                                                                   FStar_Syntax_Util.exp_unit in
                                                               FStar_Tactics_Monad.bind
                                                                 uu____5114
                                                                 (fun
                                                                    uu____5122
                                                                    ->
                                                                    let is_free_uvar
                                                                    uv t1 =
                                                                    let free_uvars
                                                                    =
                                                                    let uu____5149
                                                                    =
                                                                    let uu____5152
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Util.set_elements
                                                                    uu____5152 in
                                                                    FStar_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5149 in
                                                                    FStar_List.existsML
                                                                    (fun u ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars in
                                                                    let appears
                                                                    uv goals
                                                                    =
                                                                    FStar_List.existsML
                                                                    (fun g'
                                                                    ->
                                                                    let uu____5189
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5189)
                                                                    goals in
                                                                    let checkone
                                                                    t1 goals
                                                                    =
                                                                    let uu____5205
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                    match uu____5205
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____5223)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu____5249)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5266
                                                                    -> false) in
                                                                    let uu____5267
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    implicits2
                                                                    (FStar_Tactics_Monad.mapM
                                                                    (fun imp
                                                                    ->
                                                                    let uu____5308
                                                                    = imp in
                                                                    match uu____5308
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    ctx_uvar)
                                                                    ->
                                                                    let uu____5319
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____5319
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____5341)
                                                                    ->
                                                                    let uu____5366
                                                                    =
                                                                    let uu____5367
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd in
                                                                    uu____5367.FStar_Syntax_Syntax.n in
                                                                    (match uu____5366
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,
                                                                    uu____5375)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___822_5395
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___822_5395.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___822_5395.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___822_5395.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___822_5395.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    FStar_Tactics_Monad.ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5398
                                                                    ->
                                                                    FStar_Tactics_Monad.mlog
                                                                    (fun
                                                                    uu____5404
                                                                    ->
                                                                    let uu____5405
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                                                                    let uu____5406
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5405
                                                                    uu____5406)
                                                                    (fun
                                                                    uu____5410
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env1
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                                    let uu____5412
                                                                    =
                                                                    let uu____5415
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5416
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar in
                                                                    let uu____5417
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5416
                                                                    uu____5417
                                                                    else
                                                                    "apply_lemma solved arg" in
                                                                    proc_guard
                                                                    uu____5415
                                                                    env1
                                                                    g_typ in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5412
                                                                    (fun
                                                                    uu____5422
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    [])))))) in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5267
                                                                    (fun
                                                                    sub_goals
                                                                    ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____5484
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____5484
                                                                    then
                                                                    let uu____5487
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____5487
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu____5501
                                                                    =
                                                                    let uu____5502
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu____5502
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____5501)
                                                                    sub_goals1 in
                                                                    let uu____5503
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5503
                                                                    (fun
                                                                    uu____5509
                                                                    ->
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu____5511
                                                                    =
                                                                    let uu____5514
                                                                    =
                                                                    let uu____5515
                                                                    =
                                                                    let uu____5516
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre_u
                                                                    pre1 in
                                                                    istrivial
                                                                    env1
                                                                    uu____5516 in
                                                                    Prims.op_Negation
                                                                    uu____5515 in
                                                                    if
                                                                    uu____5514
                                                                    then
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    else
                                                                    FStar_Tactics_Monad.ret
                                                                    () in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5511
                                                                    (fun
                                                                    uu____5521
                                                                    ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2))))))))))))) in
          focus uu____4310 in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply_lemma")
          uu____4307
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar ->
    fun e ->
      let rec aux e1 =
        let uu____5572 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____5572 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu____5607 = FStar_Syntax_Syntax.bv_eq bvar bv' in
            if uu____5607
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____5629 = aux e' in
               FStar_Util.map_opt uu____5629
                 (fun uu____5660 ->
                    match uu____5660 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu____5686 = aux e in
      FStar_Util.map_opt uu____5686
        (fun uu____5717 ->
           match uu____5717 with
           | (e', bv, bvs) -> (e', bv, (FStar_List.rev bvs)))
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e ->
    fun bvs ->
      FStar_List.fold_left
        (fun e1 -> fun b -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Tactics_Types.goal ->
        (FStar_Syntax_Syntax.bv * FStar_Tactics_Types.goal)
          FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun b1 ->
    fun b2 ->
      fun g ->
        let uu____5792 =
          let uu____5803 = FStar_Tactics_Types.goal_env g in
          split_env b1 uu____5803 in
        match uu____5792 with
        | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs) in
            let t = FStar_Tactics_Types.goal_type g in
            let uu____5843 =
              let uu____5856 = FStar_Syntax_Subst.close_binders bs in
              let uu____5865 = FStar_Syntax_Subst.close bs t in
              (uu____5856, uu____5865) in
            (match uu____5843 with
             | (bs', t') ->
                 let bs'1 =
                   let uu____5909 = FStar_Syntax_Syntax.mk_binder b2 in
                   let uu____5916 = FStar_List.tail bs' in uu____5909 ::
                     uu____5916 in
                 let uu____5937 = FStar_Syntax_Subst.open_term bs'1 t' in
                 (match uu____5937 with
                  | (bs'', t'') ->
                      let b21 =
                        let uu____5953 = FStar_List.hd bs'' in
                        FStar_Pervasives_Native.fst uu____5953 in
                      let new_env =
                        let uu____5969 =
                          FStar_List.map FStar_Pervasives_Native.fst bs'' in
                        push_bvs e0 uu____5969 in
                      let uu____5980 =
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t'' in
                      FStar_Tactics_Monad.bind uu____5980
                        (fun uu____6003 ->
                           match uu____6003 with
                           | (uvt, uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label in
                               let sol =
                                 let uu____6022 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None in
                                 let uu____6025 =
                                   FStar_List.map
                                     (fun uu____6046 ->
                                        match uu____6046 with
                                        | (bv, q) ->
                                            let uu____6059 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____6059) bs in
                                 FStar_Syntax_Util.mk_app uu____6022
                                   uu____6025 in
                               let uu____6060 = set_solution g sol in
                               FStar_Tactics_Monad.bind uu____6060
                                 (fun uu____6070 ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h ->
    let uu____6108 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6116 = h in
           match uu____6116 with
           | (bv, uu____6120) ->
               FStar_Tactics_Monad.mlog
                 (fun uu____6128 ->
                    let uu____6129 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____6130 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6129
                      uu____6130)
                 (fun uu____6133 ->
                    let uu____6134 =
                      let uu____6145 = FStar_Tactics_Types.goal_env goal in
                      split_env bv uu____6145 in
                    match uu____6134 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.fail
                          "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                        let uu____6171 =
                          let uu____6178 =
                            whnf e0 bv1.FStar_Syntax_Syntax.sort in
                          destruct_eq uu____6178 in
                        (match uu____6171 with
                         | FStar_Pervasives_Native.Some (x, e) ->
                             let uu____6187 =
                               let uu____6188 = FStar_Syntax_Subst.compress x in
                               uu____6188.FStar_Syntax_Syntax.n in
                             (match uu____6187 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                  let t = FStar_Tactics_Types.goal_type goal in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs in
                                  let uu____6215 =
                                    let uu____6220 =
                                      FStar_Syntax_Subst.close_binders bs in
                                    let uu____6221 =
                                      FStar_Syntax_Subst.close bs t in
                                    (uu____6220, uu____6221) in
                                  (match uu____6215 with
                                   | (bs', t') ->
                                       let uu____6226 =
                                         let uu____6231 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs' in
                                         let uu____6232 =
                                           FStar_Syntax_Subst.subst s t in
                                         (uu____6231, uu____6232) in
                                       (match uu____6226 with
                                        | (bs'1, t'1) ->
                                            let uu____6237 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1 in
                                            (match uu____6237 with
                                             | (bs'', t'') ->
                                                 let new_env =
                                                   let uu____6247 =
                                                     let uu____6250 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs'' in
                                                     bv1 :: uu____6250 in
                                                   push_bvs e0 uu____6247 in
                                                 let uu____6261 =
                                                   FStar_Tactics_Monad.new_uvar
                                                     "rewrite" new_env t'' in
                                                 FStar_Tactics_Monad.bind
                                                   uu____6261
                                                   (fun uu____6278 ->
                                                      match uu____6278 with
                                                      | (uvt, uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label in
                                                          let sol =
                                                            let uu____6291 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None in
                                                            let uu____6294 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____6315
                                                                   ->
                                                                   match uu____6315
                                                                   with
                                                                   | 
                                                                   (bv2,
                                                                    uu____6323)
                                                                    ->
                                                                    let uu____6328
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____6328)
                                                                bs in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____6291
                                                              uu____6294 in
                                                          let uu____6329 =
                                                            set_solution goal
                                                              sol in
                                                          FStar_Tactics_Monad.bind
                                                            uu____6329
                                                            (fun uu____6333
                                                               ->
                                                               FStar_Tactics_Monad.replace_cur
                                                                 goal')))))
                              | uu____6334 ->
                                  FStar_Tactics_Monad.fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6335 ->
                             FStar_Tactics_Monad.fail
                               "Not an equality hypothesis"))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rewrite") uu____6108
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu____6360 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6382 = b in
             match uu____6382 with
             | (bv, q) ->
                 let bv' =
                   let uu____6398 =
                     let uu___944_6399 = bv in
                     let uu____6400 =
                       let uu____6401 =
                         let uu____6406 =
                           FStar_Ident.range_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         (s, uu____6406) in
                       FStar_Ident.mk_ident uu____6401 in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6400;
                       FStar_Syntax_Syntax.index =
                         (uu___944_6399.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___944_6399.FStar_Syntax_Syntax.sort)
                     } in
                   FStar_Syntax_Syntax.freshen_bv uu____6398 in
                 let uu____6407 = subst_goal bv bv' goal in
                 FStar_Tactics_Monad.bind uu____6407
                   (fun uu___4_6429 ->
                      match uu___4_6429 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Tactics_Monad.fail
                            "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                          let uu____6460 =
                            FStar_Tactics_Monad.replace_cur goal1 in
                          FStar_Tactics_Monad.bind uu____6460
                            (fun uu____6470 ->
                               FStar_Tactics_Monad.ret (bv'1, q)))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rename_to")
        uu____6360
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu____6504 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6513 = b in
           match uu____6513 with
           | (bv, uu____6517) ->
               let uu____6522 =
                 let uu____6533 = FStar_Tactics_Types.goal_env goal in
                 split_env bv uu____6533 in
               (match uu____6522 with
                | FStar_Pervasives_Native.None ->
                    FStar_Tactics_Monad.fail
                      "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu____6559 = FStar_Syntax_Util.type_u () in
                    (match uu____6559 with
                     | (ty, u) ->
                         let uu____6568 =
                           FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty in
                         FStar_Tactics_Monad.bind uu____6568
                           (fun uu____6586 ->
                              match uu____6586 with
                              | (t', u_t') ->
                                  let bv'' =
                                    let uu___971_6596 = bv1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___971_6596.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___971_6596.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    } in
                                  let s =
                                    let uu____6600 =
                                      let uu____6601 =
                                        let uu____6608 =
                                          FStar_Syntax_Syntax.bv_to_name bv'' in
                                        (bv1, uu____6608) in
                                      FStar_Syntax_Syntax.NT uu____6601 in
                                    [uu____6600] in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1 ->
                                         let uu___976_6620 = b1 in
                                         let uu____6621 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___976_6620.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___976_6620.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6621
                                         }) bvs in
                                  let env' = push_bvs e0 (bv'' :: bvs1) in
                                  FStar_Tactics_Monad.bind
                                    FStar_Tactics_Monad.dismiss
                                    (fun uu____6628 ->
                                       let new_goal =
                                         let uu____6630 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env' in
                                         let uu____6631 =
                                           let uu____6632 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           FStar_Syntax_Subst.subst s
                                             uu____6632 in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6630 uu____6631 in
                                       let uu____6633 =
                                         FStar_Tactics_Monad.add_goals
                                           [new_goal] in
                                       FStar_Tactics_Monad.bind uu____6633
                                         (fun uu____6638 ->
                                            let uu____6639 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t' in
                                            FStar_Tactics_Monad.add_irrelevant_goal
                                              goal "binder_retype equation"
                                              e0 uu____6639)))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "binder_retype")
      uu____6504
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu____6662 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6671 = b in
             match uu____6671 with
             | (bv, uu____6675) ->
                 let uu____6680 =
                   let uu____6691 = FStar_Tactics_Types.goal_env goal in
                   split_env bv uu____6691 in
                 (match uu____6680 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Tactics_Monad.fail
                        "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                      let steps =
                        let uu____6720 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6720 in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                      let bv' =
                        let uu___997_6725 = bv1 in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___997_6725.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___997_6725.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        } in
                      let env' = push_bvs e0 (bv' :: bvs) in
                      let uu____6727 =
                        FStar_Tactics_Types.goal_with_env goal env' in
                      FStar_Tactics_Monad.replace_cur uu____6727)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_binder_type")
        uu____6662
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6738 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6744 =
           let uu____6751 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6751 in
         match uu____6744 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x, env') ->
             let typ' =
               let uu____6767 =
                 let uu____6770 = FStar_Tactics_Types.goal_type goal in
                 FStar_Syntax_Syntax.mk_Total uu____6770 in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6767 in
             let uu____6785 = FStar_Tactics_Monad.new_uvar "revert" env' typ' in
             FStar_Tactics_Monad.bind uu____6785
               (fun uu____6800 ->
                  match uu____6800 with
                  | (r, u_r) ->
                      let uu____6809 =
                        let uu____6812 =
                          let uu____6813 =
                            let uu____6814 =
                              let uu____6823 =
                                FStar_Syntax_Syntax.bv_to_name x in
                              FStar_Syntax_Syntax.as_arg uu____6823 in
                            [uu____6814] in
                          let uu____6840 =
                            let uu____6841 =
                              FStar_Tactics_Types.goal_type goal in
                            uu____6841.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.mk_Tm_app r uu____6813
                            uu____6840 in
                        set_solution goal uu____6812 in
                      FStar_Tactics_Monad.bind uu____6809
                        (fun uu____6846 ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label in
                           FStar_Tactics_Monad.replace_cur g)))
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu____6858 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____6858
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = FStar_Pervasives_Native.fst b in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____6878 ->
              let uu____6879 = FStar_Syntax_Print.binder_to_string b in
              let uu____6880 =
                let uu____6881 =
                  let uu____6882 =
                    let uu____6891 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.all_binders uu____6891 in
                  FStar_All.pipe_right uu____6882 FStar_List.length in
                FStar_All.pipe_right uu____6881 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6879 uu____6880)
           (fun uu____6908 ->
              let uu____6909 =
                let uu____6920 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu____6920 in
              match uu____6909 with
              | FStar_Pervasives_Native.None ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu____6964 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu____6964
                        then
                          let uu____6967 =
                            let uu____6968 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6968 in
                          FStar_Tactics_Monad.fail uu____6967
                        else check bvs2 in
                  let uu____6970 =
                    let uu____6971 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu____6971 in
                  if uu____6970
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu____6975 = check bvs in
                     FStar_Tactics_Monad.bind uu____6975
                       (fun uu____6981 ->
                          let env' = push_bvs e' bvs in
                          let uu____6983 =
                            let uu____6990 =
                              FStar_Tactics_Types.goal_type goal in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu____6990 in
                          FStar_Tactics_Monad.bind uu____6983
                            (fun uu____6999 ->
                               match uu____6999 with
                               | (ut, uvar_ut) ->
                                   let uu____7008 = set_solution goal ut in
                                   FStar_Tactics_Monad.bind uu____7008
                                     (fun uu____7013 ->
                                        let uu____7014 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        FStar_Tactics_Monad.replace_cur
                                          uu____7014))))))
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7021 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____7027 =
           let uu____7034 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____7034 in
         match uu____7027 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu____7042) ->
             let uu____7047 = FStar_Syntax_Syntax.mk_binder x in
             clear uu____7047)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____7064 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7064 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____7082 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7082 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (_trefl :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun l ->
    fun r ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7101 =
             let uu____7104 = FStar_Tactics_Types.goal_env g in
             do_unify uu____7104 l r in
           FStar_Tactics_Monad.bind uu____7101
             (fun b ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____7111 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7111 l in
                   let r1 =
                     let uu____7113 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7113 r in
                   let uu____7114 =
                     let uu____7117 = FStar_Tactics_Types.goal_env g in
                     do_unify uu____7117 l1 r1 in
                   FStar_Tactics_Monad.bind uu____7114
                     (fun b1 ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____7123 =
                             let uu____7128 =
                               let uu____7133 =
                                 FStar_Tactics_Types.goal_env g in
                               tts uu____7133 in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____7128 l1 r1 in
                           match uu____7123 with
                           | (ls, rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
let (trefl : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7144 ->
    let uu____7147 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7155 =
             let uu____7162 =
               let uu____7163 = FStar_Tactics_Types.goal_env g in
               let uu____7164 = FStar_Tactics_Types.goal_type g in
               whnf uu____7163 uu____7164 in
             destruct_eq uu____7162 in
           match uu____7155 with
           | FStar_Pervasives_Native.Some (l, r) -> _trefl l r
           | FStar_Pervasives_Native.None ->
               let uu____7177 =
                 let uu____7178 = FStar_Tactics_Types.goal_env g in
                 let uu____7179 = FStar_Tactics_Types.goal_type g in
                 tts uu____7178 uu____7179 in
               fail1 "not an equality (%s)" uu____7177) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____7147
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7190 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let env1 = FStar_Tactics_Types.goal_env g in
         let uu____7198 =
           let uu____7205 = FStar_Tactics_Types.goal_type g in
           FStar_Tactics_Monad.new_uvar "dup" env1 uu____7205 in
         FStar_Tactics_Monad.bind uu____7198
           (fun uu____7214 ->
              match uu____7214 with
              | (u, u_uvar) ->
                  let g' =
                    let uu___1083_7224 = g in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1083_7224.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1083_7224.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1083_7224.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1083_7224.FStar_Tactics_Types.label)
                    } in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____7228 ->
                       let t_eq =
                         let uu____7230 =
                           let uu____7231 = FStar_Tactics_Types.goal_type g in
                           env1.FStar_TypeChecker_Env.universe_of env1
                             uu____7231 in
                         let uu____7232 = FStar_Tactics_Types.goal_type g in
                         let uu____7233 = FStar_Tactics_Types.goal_witness g in
                         FStar_Syntax_Util.mk_eq2 uu____7230 uu____7232 u
                           uu____7233 in
                       let uu____7234 =
                         FStar_Tactics_Monad.add_irrelevant_goal g
                           "dup equation" env1 t_eq in
                       FStar_Tactics_Monad.bind uu____7234
                         (fun uu____7239 ->
                            let uu____7240 =
                              FStar_Tactics_Monad.add_goals [g'] in
                            FStar_Tactics_Monad.bind uu____7240
                              (fun uu____7244 -> FStar_Tactics_Monad.ret ())))))
let longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs, y::ys) ->
              let uu____7367 = f x y in
              if uu____7367 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____7387 -> (acc, l11, l21) in
        let uu____7402 = aux [] l1 l2 in
        match uu____7402 with | (pr, t1, t2) -> ((FStar_List.rev pr), t1, t2)
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal ->
      FStar_Tactics_Types.goal FStar_Tactics_Monad.tac)
  =
  fun g1 ->
    fun g2 ->
      let close_forall_no_univs bs f =
        FStar_List.fold_right
          (fun b ->
             fun f1 ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f in
      let uu____7507 = FStar_Tactics_Types.get_phi g1 in
      match uu____7507 with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____7513 = FStar_Tactics_Types.get_phi g2 in
          (match uu____7513 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu____7525 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2) in
               (match uu____7525 with
                | (gamma, r1, r2) ->
                    let t1 =
                      let uu____7556 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1) in
                      close_forall_no_univs uu____7556 phi1 in
                    let t2 =
                      let uu____7566 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2) in
                      close_forall_no_univs uu____7566 phi2 in
                    let uu____7575 =
                      set_solution g1 FStar_Syntax_Util.exp_unit in
                    FStar_Tactics_Monad.bind uu____7575
                      (fun uu____7580 ->
                         let uu____7581 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.bind uu____7581
                           (fun uu____7588 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___1135_7593 =
                                  FStar_Tactics_Types.goal_env g1 in
                                let uu____7594 =
                                  FStar_Util.smap_create (Prims.of_int (100)) in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1135_7593.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1135_7593.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1135_7593.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1135_7593.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____7594;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1135_7593.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1135_7593.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1135_7593.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1135_7593.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1135_7593.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1135_7593.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1135_7593.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1135_7593.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1135_7593.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1135_7593.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1135_7593.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1135_7593.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1135_7593.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1135_7593.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1135_7593.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1135_7593.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1135_7593.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1135_7593.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1135_7593.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1135_7593.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1135_7593.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1135_7593.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1135_7593.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1135_7593.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1135_7593.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1135_7593.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1135_7593.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1135_7593.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1135_7593.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1135_7593.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1135_7593.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1135_7593.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1135_7593.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1135_7593.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1135_7593.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1135_7593.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1135_7593.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1135_7593.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1135_7593.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1135_7593.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1135_7593.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____7597 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              FStar_Tactics_Monad.bind uu____7597
                                (fun goal ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu____7606 ->
                                        let uu____7607 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1 in
                                        let uu____7608 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2 in
                                        let uu____7609 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____7607 uu____7608 uu____7609)
                                     (fun uu____7611 ->
                                        FStar_Tactics_Monad.ret goal))))))
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7618 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____7634 =
               FStar_Tactics_Monad.set
                 (let uu___1150_7639 = ps in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1150_7639.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1150_7639.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1150_7639.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1150_7639.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1150_7639.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1150_7639.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1150_7639.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1150_7639.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1150_7639.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1150_7639.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1150_7639.FStar_Tactics_Types.local_state)
                  }) in
             FStar_Tactics_Monad.bind uu____7634
               (fun uu____7642 ->
                  let uu____7643 = join_goals g1 g2 in
                  FStar_Tactics_Monad.bind uu____7643
                    (fun g12 -> FStar_Tactics_Monad.add_goals [g12]))
         | uu____7648 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu____7660 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           FStar_Options.push ();
           (let uu____7673 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
            FStar_Options.set uu____7673);
           (let res = FStar_Options.set_options s in
            let opts' = FStar_Options.peek () in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success ->
                 let g' =
                   let uu___1161_7680 = g in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1161_7680.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1161_7680.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1161_7680.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1161_7680.FStar_Tactics_Types.label)
                   } in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "set_options")
      uu____7660
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu____7692 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_All.pipe_left FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____7705 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let uu____7711 =
           (FStar_Options.lax ()) ||
             (let uu____7713 = FStar_Tactics_Types.goal_env g in
              uu____7713.FStar_TypeChecker_Env.lax) in
         FStar_Tactics_Monad.ret uu____7711)
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu____7728 =
        FStar_Tactics_Monad.mlog
          (fun uu____7733 ->
             let uu____7734 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "unquote: tm = %s\n" uu____7734)
          (fun uu____7736 ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal ->
                  let env1 =
                    let uu____7742 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu____7742 ty in
                  let uu____7743 = __tc_ghost env1 tm in
                  FStar_Tactics_Monad.bind uu____7743
                    (fun uu____7762 ->
                       match uu____7762 with
                       | (tm1, typ, guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu____7776 ->
                                let uu____7777 =
                                  FStar_Syntax_Print.term_to_string tm1 in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____7777)
                             (fun uu____7779 ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu____7782 ->
                                     let uu____7783 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____7783)
                                  (fun uu____7786 ->
                                     let uu____7787 =
                                       proc_guard "unquote" env1 guard in
                                     FStar_Tactics_Monad.bind uu____7787
                                       (fun uu____7791 ->
                                          FStar_Tactics_Monad.ret tm1)))))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unquote") uu____7728
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      let uu____7814 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> FStar_Tactics_Monad.ret ty1
        | FStar_Pervasives_Native.None ->
            let uu____7820 =
              let uu____7827 =
                let uu____7828 = FStar_Syntax_Util.type_u () in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7828 in
              FStar_Tactics_Monad.new_uvar "uvar_env.2" env1 uu____7827 in
            FStar_Tactics_Monad.bind uu____7820
              (fun uu____7844 ->
                 match uu____7844 with
                 | (typ, uvar_typ) -> FStar_Tactics_Monad.ret typ) in
      FStar_Tactics_Monad.bind uu____7814
        (fun typ ->
           let uu____7856 = FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ in
           FStar_Tactics_Monad.bind uu____7856
             (fun uu____7870 ->
                match uu____7870 with
                | (t, uvar_t) -> FStar_Tactics_Monad.ret t))
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____7888 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           let env1 = ps.FStar_Tactics_Types.main_context in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7907 -> g.FStar_Tactics_Types.opts
             | uu____7910 -> FStar_Options.peek () in
           let uu____7913 = FStar_Syntax_Util.head_and_args t in
           match uu____7913 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar, uu____7933);
                FStar_Syntax_Syntax.pos = uu____7934;
                FStar_Syntax_Syntax.vars = uu____7935;_},
              uu____7936) ->
               let env2 =
                 let uu___1215_7978 = env1 in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1215_7978.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1215_7978.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1215_7978.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1215_7978.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1215_7978.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1215_7978.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1215_7978.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1215_7978.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1215_7978.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1215_7978.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1215_7978.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1215_7978.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1215_7978.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1215_7978.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1215_7978.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1215_7978.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1215_7978.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1215_7978.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1215_7978.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1215_7978.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1215_7978.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1215_7978.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1215_7978.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1215_7978.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1215_7978.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1215_7978.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1215_7978.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1215_7978.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1215_7978.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1215_7978.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1215_7978.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1215_7978.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1215_7978.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1215_7978.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1215_7978.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1215_7978.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1215_7978.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1215_7978.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1215_7978.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1215_7978.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1215_7978.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1215_7978.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1215_7978.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1215_7978.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1215_7978.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___1215_7978.FStar_TypeChecker_Env.enable_defer_to_tac)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
               let uu____7980 = let uu____7983 = bnorm_goal g in [uu____7983] in
               FStar_Tactics_Monad.add_goals uu____7980
           | uu____7984 -> FStar_Tactics_Monad.fail "not a uvar") in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unshelve") uu____7888
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b ->
             let uu____8033 = if b then t2 else FStar_Tactics_Monad.ret false in
             FStar_Tactics_Monad.bind uu____8033
               (fun b' ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail "")) in
      let uu____8044 = trytac comp in
      FStar_Tactics_Monad.bind uu____8044
        (fun uu___5_8052 ->
           match uu___5_8052 with
           | FStar_Pervasives_Native.Some (true) ->
               FStar_Tactics_Monad.ret true
           | FStar_Pervasives_Native.Some (false) -> failwith "impossible"
           | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret false)
let (match_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____8078 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____8084 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____8084
                 (fun uu____8104 ->
                    match uu____8104 with
                    | (t11, ty1, g1) ->
                        let uu____8116 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____8116
                          (fun uu____8136 ->
                             match uu____8136 with
                             | (t21, ty2, g2) ->
                                 let uu____8148 =
                                   proc_guard "match_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8148
                                   (fun uu____8153 ->
                                      let uu____8154 =
                                        proc_guard "match_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8154
                                        (fun uu____8160 ->
                                           let uu____8161 =
                                             do_match e ty1 ty2 in
                                           let uu____8164 =
                                             do_match e t11 t21 in
                                           tac_and uu____8161 uu____8164))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "match_env")
          uu____8078
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____8190 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____8196 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____8196
                 (fun uu____8216 ->
                    match uu____8216 with
                    | (t11, ty1, g1) ->
                        let uu____8228 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____8228
                          (fun uu____8248 ->
                             match uu____8248 with
                             | (t21, ty2, g2) ->
                                 let uu____8260 =
                                   proc_guard "unify_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8260
                                   (fun uu____8265 ->
                                      let uu____8266 =
                                        proc_guard "unify_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8266
                                        (fun uu____8272 ->
                                           let uu____8273 =
                                             do_unify e ty1 ty2 in
                                           let uu____8276 =
                                             do_unify e t11 t21 in
                                           tac_and uu____8273 uu____8276))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unify_env")
          uu____8190
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____8309 ->
             let uu____8310 = FStar_Options.unsafe_tactic_exec () in
             if uu____8310
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input) in
               FStar_Tactics_Monad.ret s
             else
               FStar_Tactics_Monad.fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let (fresh_bv_named :
  Prims.string ->
    FStar_Reflection_Data.typ ->
      FStar_Syntax_Syntax.bv FStar_Tactics_Monad.tac)
  =
  fun nm ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
        (fun uu____8331 ->
           let uu____8332 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t in
           FStar_Tactics_Monad.ret uu____8332)
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu____8342 =
      FStar_Tactics_Monad.mlog
        (fun uu____8347 ->
           let uu____8348 = FStar_Syntax_Print.term_to_string ty in
           FStar_Util.print1 "change: ty = %s\n" uu____8348)
        (fun uu____8350 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                let uu____8354 =
                  let uu____8363 = FStar_Tactics_Types.goal_env g in
                  __tc uu____8363 ty in
                FStar_Tactics_Monad.bind uu____8354
                  (fun uu____8375 ->
                     match uu____8375 with
                     | (ty1, uu____8385, guard) ->
                         let uu____8387 =
                           let uu____8390 = FStar_Tactics_Types.goal_env g in
                           proc_guard "change" uu____8390 guard in
                         FStar_Tactics_Monad.bind uu____8387
                           (fun uu____8393 ->
                              let uu____8394 =
                                let uu____8397 =
                                  FStar_Tactics_Types.goal_env g in
                                let uu____8398 =
                                  FStar_Tactics_Types.goal_type g in
                                do_unify uu____8397 uu____8398 ty1 in
                              FStar_Tactics_Monad.bind uu____8394
                                (fun bb ->
                                   if bb
                                   then
                                     let uu____8404 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1 in
                                     FStar_Tactics_Monad.replace_cur
                                       uu____8404
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu____8410 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu____8411 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu____8410 uu____8411 in
                                      let nty =
                                        let uu____8413 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu____8413 ty1 in
                                      let uu____8414 =
                                        let uu____8417 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify uu____8417 ng nty in
                                      FStar_Tactics_Monad.bind uu____8414
                                        (fun b ->
                                           if b
                                           then
                                             let uu____8423 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1 in
                                             FStar_Tactics_Monad.replace_cur
                                               uu____8423
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible"))))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "change") uu____8342
let failwhen :
  'a .
    Prims.bool ->
      Prims.string ->
        (unit -> 'a FStar_Tactics_Monad.tac) -> 'a FStar_Tactics_Monad.tac
  =
  fun b ->
    fun msg -> fun k -> if b then FStar_Tactics_Monad.fail msg else k ()
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list
      FStar_Tactics_Monad.tac)
  =
  fun s_tm ->
    let uu____8486 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____8504 =
             let uu____8513 = FStar_Tactics_Types.goal_env g in
             __tc uu____8513 s_tm in
           FStar_Tactics_Monad.bind uu____8504
             (fun uu____8531 ->
                match uu____8531 with
                | (s_tm1, s_ty, guard) ->
                    let uu____8549 =
                      let uu____8552 = FStar_Tactics_Types.goal_env g in
                      proc_guard "destruct" uu____8552 guard in
                    FStar_Tactics_Monad.bind uu____8549
                      (fun uu____8565 ->
                         let s_ty1 =
                           let uu____8567 = FStar_Tactics_Types.goal_env g in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu____8567
                             s_ty in
                         let uu____8568 =
                           let uu____8583 = FStar_Syntax_Util.unrefine s_ty1 in
                           FStar_Syntax_Util.head_and_args' uu____8583 in
                         match uu____8568 with
                         | (h, args) ->
                             let uu____8614 =
                               let uu____8621 =
                                 let uu____8622 =
                                   FStar_Syntax_Subst.compress h in
                                 uu____8622.FStar_Syntax_Syntax.n in
                               match uu____8621 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____8637;
                                      FStar_Syntax_Syntax.vars = uu____8638;_},
                                    us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu____8648 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv" in
                             FStar_Tactics_Monad.bind uu____8614
                               (fun uu____8668 ->
                                  match uu____8668 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu____8684 =
                                        let uu____8687 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____8687 t_lid in
                                      (match uu____8684 with
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Tactics_Monad.fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid, t_us, t_ps, t_ty, mut,
                                                 c_lids)
                                                ->
                                                let erasable =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr in
                                                let uu____8726 =
                                                  erasable &&
                                                    (let uu____8728 =
                                                       FStar_Tactics_Types.is_irrelevant
                                                         g in
                                                     Prims.op_Negation
                                                       uu____8728) in
                                                failwhen uu____8726
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____8736 ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____8748 ->
                                                          let uu____8749 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty in
                                                          match uu____8749
                                                          with
                                                          | (t_ps1, t_ty1) ->
                                                              let uu____8764
                                                                =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid
                                                                    ->
                                                                    let uu____8792
                                                                    =
                                                                    let uu____8795
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____8795
                                                                    c_lid in
                                                                    match uu____8792
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "ctor not found?"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    (_c_lid,
                                                                    c_us,
                                                                    c_ty,
                                                                    _t_lid,
                                                                    nparam,
                                                                    mut1) ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor) in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____8868
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu____8873
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu____8873
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu____8896
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu____8896
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu____8915
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu____8938
                                                                    =
                                                                    let uu____8943
                                                                    =
                                                                    let uu____8944
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    ppname in
                                                                    Prims.op_Hat
                                                                    "a"
                                                                    uu____8944 in
                                                                    let uu____8945
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu____8943,
                                                                    uu____8945) in
                                                                    FStar_Ident.mk_ident
                                                                    uu____8938 in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1357_8948
                                                                    = bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1357_8948.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1357_8948.FStar_Syntax_Syntax.sort)
                                                                    }) in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____8974
                                                                    ->
                                                                    match uu____8974
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    let uu____8993
                                                                    =
                                                                    rename_bv
                                                                    bv in
                                                                    (uu____8993,
                                                                    aq)) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____9018
                                                                    ->
                                                                    fun
                                                                    uu____9019
                                                                    ->
                                                                    match 
                                                                    (uu____9018,
                                                                    uu____9019)
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9045),
                                                                    (bv',
                                                                    uu____9047))
                                                                    ->
                                                                    let uu____9068
                                                                    =
                                                                    let uu____9075
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu____9075) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9068)
                                                                    bs bs' in
                                                                    let uu____9080
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu____9089
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu____9080,
                                                                    uu____9089) in
                                                                    (match uu____8915
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu____9136
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu____9136
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu____9209
                                                                    =
                                                                    let uu____9210
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu____9210 in
                                                                    failwhen
                                                                    uu____9209
                                                                    "not total?"
                                                                    (fun
                                                                    uu____9227
                                                                    ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    } in
                                                                    let is_imp
                                                                    uu___6_9243
                                                                    =
                                                                    match uu___6_9243
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____9246)
                                                                    -> true
                                                                    | 
                                                                    uu____9247
                                                                    -> false in
                                                                    let uu____9250
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu____9250
                                                                    with
                                                                    | 
                                                                    (a_ps,
                                                                    a_is) ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____9385
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9447
                                                                    ->
                                                                    match uu____9447
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9467),
                                                                    (t,
                                                                    uu____9469))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps in
                                                                    let bs3 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs2 in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9537
                                                                    ->
                                                                    match uu____9537
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9563),
                                                                    (t,
                                                                    uu____9565))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9620
                                                                    ->
                                                                    match uu____9620
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs3 in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2 in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats)) in
                                                                    let env1
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g in
                                                                    let equ =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1
                                                                    s_ty1 in
                                                                    let uu____9670
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1416_9693
                                                                    = env1 in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1416_9693.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    }) s_ty1
                                                                    pat in
                                                                    match uu____9670
                                                                    with
                                                                    | 
                                                                    (uu____9706,
                                                                    uu____9707,
                                                                    uu____9708,
                                                                    uu____9709,
                                                                    pat_t,
                                                                    uu____9711,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____9723
                                                                    =
                                                                    let uu____9724
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____9724 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____9723 in
                                                                    let cod1
                                                                    =
                                                                    let uu____9728
                                                                    =
                                                                    let uu____9737
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu____9737] in
                                                                    let uu____9756
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9728
                                                                    uu____9756 in
                                                                    let nty =
                                                                    let uu____9762
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____9762 in
                                                                    let uu____9765
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9765
                                                                    (fun
                                                                    uu____9794
                                                                    ->
                                                                    match uu____9794
                                                                    with
                                                                    | 
                                                                    (uvt, uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env1 uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs3 in
                                                                    let brt1
                                                                    =
                                                                    let uu____9820
                                                                    =
                                                                    let uu____9831
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu____9831] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____9820 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu____9867
                                                                    =
                                                                    let uu____9878
                                                                    =
                                                                    let uu____9883
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu____9883) in
                                                                    (g', br,
                                                                    uu____9878) in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu____9867)))))))
                                                                    | 
                                                                    uu____9904
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids in
                                                              FStar_Tactics_Monad.bind
                                                                uu____8764
                                                                (fun goal_brs
                                                                   ->
                                                                   let uu____9953
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs in
                                                                   match uu____9953
                                                                   with
                                                                   | 
                                                                   (goals,
                                                                    brs,
                                                                    infos) ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    s_tm1.FStar_Syntax_Syntax.pos in
                                                                    let uu____10026
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10026
                                                                    (fun
                                                                    uu____10037
                                                                    ->
                                                                    let uu____10038
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10038
                                                                    (fun
                                                                    uu____10048
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos)))))
                                            | uu____10055 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type")))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "destruct") uu____8486
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10100::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10128 = init xs in x :: uu____10128
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t ->
    let uu____10140 =
      let uu____10143 = top_env () in
      FStar_Tactics_Monad.bind uu____10143
        (fun e ->
           let t1 = FStar_Syntax_Util.unascribe t in
           let t2 = FStar_Syntax_Util.un_uinst t1 in
           let t3 = FStar_Syntax_Util.unlazy_emb t2 in
           match t3.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta (t4, uu____10159) -> inspect t4
           | FStar_Syntax_Syntax.Tm_name bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Var bv)
           | FStar_Syntax_Syntax.Tm_bvar bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_BVar bv)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_FVar fv)
           | FStar_Syntax_Syntax.Tm_app (hd, []) ->
               failwith "empty arguments on Tm_app"
           | FStar_Syntax_Syntax.Tm_app (hd, args) ->
               let uu____10224 = last args in
               (match uu____10224 with
                | (a, q) ->
                    let q' = FStar_Reflection_Basic.inspect_aqual q in
                    let uu____10254 =
                      let uu____10255 =
                        let uu____10260 =
                          let uu____10261 = init args in
                          FStar_Syntax_Syntax.mk_Tm_app hd uu____10261
                            t3.FStar_Syntax_Syntax.pos in
                        (uu____10260, (a, q')) in
                      FStar_Reflection_Data.Tv_App uu____10255 in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10254)
           | FStar_Syntax_Syntax.Tm_abs ([], uu____10272, uu____10273) ->
               failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs (bs, t4, k) ->
               let uu____10325 = FStar_Syntax_Subst.open_term bs t4 in
               (match uu____10325 with
                | (bs1, t5) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu____10366 =
                           let uu____10367 =
                             let uu____10372 = FStar_Syntax_Util.abs bs2 t5 k in
                             (b, uu____10372) in
                           FStar_Reflection_Data.Tv_Abs uu____10367 in
                         FStar_All.pipe_left FStar_Tactics_Monad.ret
                           uu____10366))
           | FStar_Syntax_Syntax.Tm_type uu____10375 ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Type ())
           | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
               failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu____10399 ->
               let uu____10414 = FStar_Syntax_Util.arrow_one t3 in
               (match uu____10414 with
                | FStar_Pervasives_Native.Some (b, c) ->
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine (bv, t4) ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____10444 = FStar_Syntax_Subst.open_term [b] t4 in
               (match uu____10444 with
                | (b', t5) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu____10497 -> failwith "impossible" in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Refine
                         ((FStar_Pervasives_Native.fst b1), t5)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu____10509 =
                 let uu____10510 = FStar_Reflection_Basic.inspect_const c in
                 FStar_Reflection_Data.Tv_Const uu____10510 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10509
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
               let uu____10531 =
                 let uu____10532 =
                   let uu____10537 =
                     let uu____10538 =
                       FStar_Syntax_Unionfind.uvar_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                     FStar_BigInt.of_int_fs uu____10538 in
                   (uu____10537, (ctx_u, s)) in
                 FStar_Reflection_Data.Tv_Uvar uu____10532 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10531
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10572 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv in
                      let uu____10577 = FStar_Syntax_Subst.open_term [b] t21 in
                      (match uu____10577 with
                       | (bs, t22) ->
                           let b1 =
                             match bs with
                             | b1::[] -> b1
                             | uu____10630 ->
                                 failwith
                                   "impossible: open_term returned different amount of binders" in
                           FStar_All.pipe_left FStar_Tactics_Monad.ret
                             (FStar_Reflection_Data.Tv_Let
                                (false, (lb.FStar_Syntax_Syntax.lbattrs),
                                  (FStar_Pervasives_Native.fst b1),
                                  (lb.FStar_Syntax_Syntax.lbdef), t22))))
           | FStar_Syntax_Syntax.Tm_let ((true, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10666 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let uu____10670 =
                        FStar_Syntax_Subst.open_let_rec [lb] t21 in
                      (match uu____10670 with
                       | (lbs, t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____10690 ->
                                     FStar_Tactics_Monad.ret
                                       FStar_Reflection_Data.Tv_Unknown
                                 | FStar_Util.Inl bv1 ->
                                     FStar_All.pipe_left
                                       FStar_Tactics_Monad.ret
                                       (FStar_Reflection_Data.Tv_Let
                                          (true,
                                            (lb1.FStar_Syntax_Syntax.lbattrs),
                                            bv1,
                                            (lb1.FStar_Syntax_Syntax.lbdef),
                                            t22)))
                            | uu____10696 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match (t4, brs) ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu____10750 = FStar_Reflection_Basic.inspect_const c in
                     FStar_Reflection_Data.Pat_Constant uu____10750
                 | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
                     let uu____10769 =
                       let uu____10780 =
                         FStar_List.map
                           (fun uu____10801 ->
                              match uu____10801 with
                              | (p1, b) ->
                                  let uu____10818 = inspect_pat p1 in
                                  (uu____10818, b)) ps in
                       (fv, uu____10780) in
                     FStar_Reflection_Data.Pat_Cons uu____10769
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_Data.Pat_Var bv
                 | FStar_Syntax_Syntax.Pat_wild bv ->
                     FStar_Reflection_Data.Pat_Wild bv
                 | FStar_Syntax_Syntax.Pat_dot_term (bv, t5) ->
                     FStar_Reflection_Data.Pat_Dot_Term (bv, t5) in
               let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
               let brs2 =
                 FStar_List.map
                   (fun uu___7_10912 ->
                      match uu___7_10912 with
                      | (pat, uu____10934, t5) ->
                          let uu____10952 = inspect_pat pat in
                          (uu____10952, t5)) brs1 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Match (t4, brs2))
           | FStar_Syntax_Syntax.Tm_unknown ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 FStar_Reflection_Data.Tv_Unknown
           | uu____10961 ->
               ((let uu____10963 =
                   let uu____10968 =
                     let uu____10969 = FStar_Syntax_Print.tag_of_term t3 in
                     let uu____10970 = term_to_string e t3 in
                     FStar_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu____10969 uu____10970 in
                   (FStar_Errors.Warning_CantInspect, uu____10968) in
                 FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos
                   uu____10963);
                FStar_All.pipe_left FStar_Tactics_Monad.ret
                  FStar_Reflection_Data.Tv_Unknown)) in
    FStar_Tactics_Monad.wrap_err "inspect" uu____10140
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10983 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10983
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10987 = FStar_Syntax_Syntax.bv_to_tm bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10987
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10991 = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10991
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q in
        let uu____10998 = FStar_Syntax_Util.mk_app l [(r, q')] in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10998
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        let uu____11023 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11023
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        let uu____11040 = FStar_Syntax_Util.arrow [b] c in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11040
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left FStar_Tactics_Monad.ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        let uu____11059 = FStar_Syntax_Util.refine bv t in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11059
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11063 =
          let uu____11064 =
            let uu____11065 = FStar_Reflection_Basic.pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____11065 in
          FStar_Syntax_Syntax.mk uu____11064 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11063
    | FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) ->
        let uu____11070 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11070
    | FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11082 =
          let uu____11083 =
            let uu____11084 =
              let uu____11097 =
                let uu____11100 =
                  let uu____11101 = FStar_Syntax_Syntax.mk_binder bv in
                  [uu____11101] in
                FStar_Syntax_Subst.close uu____11100 t2 in
              ((false, [lb]), uu____11097) in
            FStar_Syntax_Syntax.Tm_let uu____11084 in
          FStar_Syntax_Syntax.mk uu____11083 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11082
    | FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11141 = FStar_Syntax_Subst.close_let_rec [lb] t2 in
        (match uu____11141 with
         | (lbs, body) ->
             let uu____11156 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Range.dummyRange in
             FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11156)
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v =
          {
            FStar_Syntax_Syntax.v = v;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11190 =
                let uu____11191 = FStar_Reflection_Basic.pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____11191 in
              FStar_All.pipe_left wrap uu____11190
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____11206 =
                let uu____11207 =
                  let uu____11220 =
                    FStar_List.map
                      (fun uu____11241 ->
                         match uu____11241 with
                         | (p1, b) ->
                             let uu____11252 = pack_pat p1 in
                             (uu____11252, b)) ps in
                  (fv, uu____11220) in
                FStar_Syntax_Syntax.Pat_cons uu____11207 in
              FStar_All.pipe_left wrap uu____11206
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___8_11298 ->
               match uu___8_11298 with
               | (pat, t1) ->
                   let uu____11315 = pack_pat pat in
                   (uu____11315, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        let uu____11363 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11363
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        let uu____11391 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11391
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        let uu____11437 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11437
    | FStar_Reflection_Data.Tv_Unknown ->
        let uu____11476 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11476
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu____11493 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             let uu____11499 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k in
             match uu____11499 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lget") uu____11493
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu____11528 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let ps1 =
                 let uu___1721_11535 = ps in
                 let uu____11536 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___1721_11535.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___1721_11535.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___1721_11535.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___1721_11535.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___1721_11535.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___1721_11535.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___1721_11535.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___1721_11535.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___1721_11535.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___1721_11535.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___1721_11535.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____11536
                 } in
               FStar_Tactics_Monad.set ps1) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lset") uu____11528
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env1 ->
    let uu____11548 = FStar_TypeChecker_Env.clear_expected_typ env1 in
    match uu____11548 with
    | (env2, uu____11556) ->
        let env3 =
          let uu___1728_11562 = env2 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1728_11562.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1728_11562.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1728_11562.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1728_11562.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1728_11562.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1728_11562.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1728_11562.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1728_11562.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1728_11562.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1728_11562.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___1728_11562.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1728_11562.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1728_11562.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1728_11562.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1728_11562.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1728_11562.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1728_11562.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1728_11562.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1728_11562.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1728_11562.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1728_11562.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1728_11562.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1728_11562.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1728_11562.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1728_11562.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1728_11562.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1728_11562.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1728_11562.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1728_11562.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1728_11562.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1728_11562.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1728_11562.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1728_11562.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1728_11562.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1728_11562.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1728_11562.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1728_11562.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1728_11562.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1728_11562.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1728_11562.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1728_11562.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1728_11562.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1728_11562.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1728_11562.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1728_11562.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1728_11562.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let env4 =
          let uu___1731_11564 = env3 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1731_11564.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1731_11564.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1731_11564.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1731_11564.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1731_11564.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1731_11564.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1731_11564.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1731_11564.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1731_11564.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1731_11564.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1731_11564.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1731_11564.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1731_11564.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1731_11564.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1731_11564.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1731_11564.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1731_11564.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1731_11564.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1731_11564.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1731_11564.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1731_11564.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1731_11564.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1731_11564.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___1731_11564.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1731_11564.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1731_11564.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1731_11564.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1731_11564.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1731_11564.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1731_11564.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1731_11564.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1731_11564.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1731_11564.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1731_11564.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1731_11564.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1731_11564.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1731_11564.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1731_11564.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1731_11564.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1731_11564.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1731_11564.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1731_11564.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1731_11564.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1731_11564.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1731_11564.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1731_11564.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        env4
let (proofstate_of_goals :
  FStar_Range.range ->
    env ->
      FStar_Tactics_Types.goal Prims.list ->
        FStar_TypeChecker_Common.implicit Prims.list ->
          FStar_Tactics_Types.proofstate)
  =
  fun rng ->
    fun env1 ->
      fun goals ->
        fun imps ->
          let env2 = tac_env env1 in
          let ps =
            let uu____11595 =
              FStar_TypeChecker_Env.debug env2
                (FStar_Options.Other "TacVerbose") in
            let uu____11596 = FStar_Util.psmap_empty () in
            {
              FStar_Tactics_Types.main_context = env2;
              FStar_Tactics_Types.all_implicits = imps;
              FStar_Tactics_Types.goals = goals;
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = Prims.int_zero;
              FStar_Tactics_Types.__dump =
                FStar_Tactics_Printing.do_dump_proofstate;
              FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
              FStar_Tactics_Types.entry_range = rng;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = Prims.int_zero;
              FStar_Tactics_Types.tac_verb_dbg = uu____11595;
              FStar_Tactics_Types.local_state = uu____11596
            } in
          ps
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun typ ->
        let env2 = tac_env env1 in
        let uu____11619 = FStar_Tactics_Types.goal_of_goal_ty env2 typ in
        match uu____11619 with
        | (g, g_u) ->
            let ps =
              proofstate_of_goals rng env2 [g]
                g_u.FStar_TypeChecker_Common.implicits in
            let uu____11631 = FStar_Tactics_Types.goal_witness g in
            (ps, uu____11631)
let (proofstate_of_all_implicits :
  FStar_Range.range ->
    env ->
      implicits ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun imps ->
        let env2 = tac_env env1 in
        let goals =
          FStar_List.map (FStar_Tactics_Types.goal_of_implicit env2) imps in
        let w =
          let uu____11656 = FStar_List.hd goals in
          FStar_Tactics_Types.goal_witness uu____11656 in
        let ps =
          let uu____11658 =
            FStar_TypeChecker_Env.debug env2
              (FStar_Options.Other "TacVerbose") in
          let uu____11659 = FStar_Util.psmap_empty () in
          {
            FStar_Tactics_Types.main_context = env2;
            FStar_Tactics_Types.all_implicits = imps;
            FStar_Tactics_Types.goals = goals;
            FStar_Tactics_Types.smt_goals = [];
            FStar_Tactics_Types.depth = Prims.int_zero;
            FStar_Tactics_Types.__dump =
              (fun ps ->
                 fun msg -> FStar_Tactics_Printing.do_dump_proofstate ps msg);
            FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu____11658;
            FStar_Tactics_Types.local_state = uu____11659
          } in
        (ps, w)