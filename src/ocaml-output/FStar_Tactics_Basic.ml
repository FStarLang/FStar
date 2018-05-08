open Prims
type goal = FStar_Tactics_Types.goal[@@deriving show]
type name = FStar_Syntax_Syntax.bv[@@deriving show]
type env = FStar_TypeChecker_Env.env[@@deriving show]
type implicits = FStar_TypeChecker_Env.implicits[@@deriving show]
let (normalize :
  FStar_TypeChecker_Normalize.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
  
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> normalize [] e t 
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string 
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g  ->
    let uu____43 =
      let uu____44 = FStar_Tactics_Types.goal_env g  in
      let uu____45 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____44 uu____45  in
    FStar_Tactics_Types.goal_with_type g uu____43
  
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
[@@deriving show]
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
  
let mk_tac :
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f  -> { tac_f = f } 
let run :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p 
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____187 = run t1 p  in
           match uu____187 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____194 = t2 a  in run uu____194 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (idtac : unit tac) = ret () 
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun goal  ->
    let uu____214 =
      FStar_Syntax_Unionfind.find
        (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
       in
    match uu____214 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____225 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____226 =
      let uu____227 = check_goal_solved g  in
      match uu____227 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____231 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____231
       in
    FStar_Util.format2 "%s%s" uu____225 uu____226
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____247 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____247
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____263 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____263
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____284 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____284
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____291) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____301) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____316 =
      let uu____321 =
        let uu____322 = FStar_Tactics_Types.goal_env g  in
        let uu____323 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____322 uu____323  in
      FStar_Syntax_Util.un_squash uu____321  in
    match uu____316 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____329 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____357 =
            let uu____358 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____358  in
          if uu____357 then tacprint msg else ());
         ret ())
  
let dump_goal : 'Auu____366 . 'Auu____366 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  -> let uu____378 = goal_to_string goal  in tacprint uu____378
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____390 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____394 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____394))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____403  ->
    match uu____403 with
    | (msg,ps) ->
        let uu____410 =
          let uu____413 =
            let uu____414 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____414 msg
             in
          let uu____415 =
            let uu____418 =
              let uu____419 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____419  in
            let uu____420 =
              let uu____423 =
                let uu____424 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____425 =
                  let uu____426 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____426  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____424
                  uu____425
                 in
              let uu____429 =
                let uu____432 =
                  let uu____433 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____434 =
                    let uu____435 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____435  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____433
                    uu____434
                   in
                [uu____432]  in
              uu____423 :: uu____429  in
            uu____418 :: uu____420  in
          uu____413 :: uu____415  in
        FStar_String.concat "" uu____410
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____444 =
        let uu____445 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____445  in
      let uu____446 =
        let uu____451 =
          let uu____452 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____452  in
        FStar_Syntax_Print.binders_to_json uu____451  in
      FStar_All.pipe_right uu____444 uu____446  in
    let uu____453 =
      let uu____460 =
        let uu____467 =
          let uu____472 =
            let uu____473 =
              let uu____480 =
                let uu____485 =
                  let uu____486 =
                    let uu____487 = FStar_Tactics_Types.goal_env g  in
                    let uu____488 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____487 uu____488  in
                  FStar_Util.JsonStr uu____486  in
                ("witness", uu____485)  in
              let uu____489 =
                let uu____496 =
                  let uu____501 =
                    let uu____502 =
                      let uu____503 = FStar_Tactics_Types.goal_env g  in
                      let uu____504 = FStar_Tactics_Types.goal_type g  in
                      tts uu____503 uu____504  in
                    FStar_Util.JsonStr uu____502  in
                  ("type", uu____501)  in
                [uu____496]  in
              uu____480 :: uu____489  in
            FStar_Util.JsonAssoc uu____473  in
          ("goal", uu____472)  in
        [uu____467]  in
      ("hyps", g_binders) :: uu____460  in
    FStar_Util.JsonAssoc uu____453
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____537  ->
    match uu____537 with
    | (msg,ps) ->
        let uu____544 =
          let uu____551 =
            let uu____558 =
              let uu____565 =
                let uu____572 =
                  let uu____577 =
                    let uu____578 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____578  in
                  ("goals", uu____577)  in
                let uu____581 =
                  let uu____588 =
                    let uu____593 =
                      let uu____594 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____594  in
                    ("smt-goals", uu____593)  in
                  [uu____588]  in
                uu____572 :: uu____581  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____565
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____558  in
          let uu____617 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____630 =
                let uu____635 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____635)  in
              [uu____630]
            else []  in
          FStar_List.append uu____551 uu____617  in
        FStar_Util.JsonAssoc uu____544
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____665  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state1 : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____688 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____688 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____706 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____706 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____739 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____739 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____770 =
              let uu____773 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____773  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____770);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____854 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____854
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____862 . Prims.string -> Prims.string -> 'Auu____862 tac =
  fun msg  ->
    fun x  -> let uu____875 = FStar_Util.format1 msg x  in fail uu____875
  
let fail2 :
  'Auu____884 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____884 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____902 = FStar_Util.format2 msg x y  in fail uu____902
  
let fail3 :
  'Auu____913 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____913 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____936 = FStar_Util.format3 msg x y z  in fail uu____936
  
let fail4 :
  'Auu____949 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____949 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____977 = FStar_Util.format4 msg x y z w  in fail uu____977
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1010 = run t ps  in
         match uu____1010 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___93_1034 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___93_1034.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___93_1034.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___93_1034.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___93_1034.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___93_1034.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___93_1034.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___93_1034.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___93_1034.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___93_1034.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___93_1034.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1061 = trytac' t  in
    bind uu____1061
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1088 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1124 = trytac t  in run uu____1124 ps
         with
         | FStar_Errors.Err (uu____1140,msg) ->
             (log ps
                (fun uu____1144  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1149,msg,uu____1151) ->
             (log ps
                (fun uu____1154  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1187 = run t ps  in
           match uu____1187 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1206  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1227 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1227
         then
           let uu____1228 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1229 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1228
             uu____1229
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1241 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1241
            then
              let uu____1242 = FStar_Util.string_of_bool res  in
              let uu____1243 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1244 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1242 uu____1243 uu____1244
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1252,msg) ->
             mlog
               (fun uu____1255  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1257  -> ret false)
         | FStar_Errors.Error (uu____1258,msg,r) ->
             mlog
               (fun uu____1263  ->
                  let uu____1264 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1264) (fun uu____1266  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1289  ->
             (let uu____1291 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1291
              then
                (FStar_Options.push ();
                 (let uu____1293 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1295 =
                let uu____1298 = __do_unify env t1 t2  in
                bind uu____1298
                  (fun b  ->
                     if Prims.op_Negation b
                     then
                       let t11 =
                         FStar_TypeChecker_Normalize.normalize [] env t1  in
                       let t21 =
                         FStar_TypeChecker_Normalize.normalize [] env t2  in
                       __do_unify env t11 t21
                     else ret b)
                 in
              bind uu____1295
                (fun r  ->
                   (let uu____1314 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1314 then FStar_Options.pop () else ());
                   ret r)))
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1330 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1330 with
      | FStar_Pervasives_Native.Some uu____1335 ->
          let uu____1336 =
            let uu____1337 = goal_to_string goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1337  in
          fail uu____1336
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1353 = FStar_Tactics_Types.goal_env goal  in
      let uu____1354 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1353 solution uu____1354
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1360 =
         let uu___98_1361 = p  in
         let uu____1362 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___98_1361.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___98_1361.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___98_1361.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1362;
           FStar_Tactics_Types.smt_goals =
             (uu___98_1361.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___98_1361.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___98_1361.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___98_1361.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___98_1361.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___98_1361.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___98_1361.FStar_Tactics_Types.freshness)
         }  in
       set uu____1360)
  
let (dismiss : unit -> unit tac) =
  fun uu____1371  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1378 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1395 = trysolve goal solution  in
      bind uu____1395
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1403 =
                let uu____1404 =
                  let uu____1405 = FStar_Tactics_Types.goal_env goal  in
                  tts uu____1405 solution  in
                let uu____1406 =
                  let uu____1407 = FStar_Tactics_Types.goal_env goal  in
                  let uu____1408 = FStar_Tactics_Types.goal_witness goal  in
                  tts uu____1407 uu____1408  in
                let uu____1409 =
                  let uu____1410 = FStar_Tactics_Types.goal_env goal  in
                  let uu____1411 = FStar_Tactics_Types.goal_type goal  in
                  tts uu____1410 uu____1411  in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1404
                  uu____1406 uu____1409
                 in
              fail uu____1403))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___99_1418 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___99_1418.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___99_1418.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___99_1418.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___99_1418.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___99_1418.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___99_1418.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___99_1418.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___99_1418.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___99_1418.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___99_1418.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1437 = FStar_Options.defensive ()  in
    if uu____1437
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1442 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1442)
         in
      let b2 =
        b1 &&
          (let uu____1445 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1445)
         in
      let rec aux b3 e =
        let uu____1457 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1457 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1475 =
        (let uu____1478 = aux b2 env  in Prims.op_Negation uu____1478) &&
          (let uu____1480 = FStar_ST.op_Bang nwarn  in
           uu____1480 < (Prims.parse_int "5"))
         in
      (if uu____1475
       then
         ((let uu____1505 =
             let uu____1506 = FStar_Tactics_Types.goal_type g  in
             uu____1506.FStar_Syntax_Syntax.pos  in
           let uu____1509 =
             let uu____1514 =
               let uu____1515 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1515
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1514)  in
           FStar_Errors.log_issue uu____1505 uu____1509);
          (let uu____1516 =
             let uu____1517 = FStar_ST.op_Bang nwarn  in
             uu____1517 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1516))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___100_1585 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___100_1585.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___100_1585.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___100_1585.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___100_1585.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___100_1585.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___100_1585.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___100_1585.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___100_1585.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___100_1585.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___100_1585.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___101_1605 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___101_1605.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___101_1605.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___101_1605.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___101_1605.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___101_1605.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___101_1605.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___101_1605.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___101_1605.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___101_1605.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___101_1605.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___102_1625 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___102_1625.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___102_1625.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___102_1625.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___102_1625.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___102_1625.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___102_1625.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___102_1625.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___102_1625.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___102_1625.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___102_1625.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___103_1645 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___103_1645.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___103_1645.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___103_1645.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___103_1645.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___103_1645.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___103_1645.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___103_1645.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___103_1645.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___103_1645.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___103_1645.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1656  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___104_1670 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___104_1670.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___104_1670.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___104_1670.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___104_1670.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___104_1670.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___104_1670.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___104_1670.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___104_1670.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___104_1670.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___104_1670.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar)
          FStar_Pervasives_Native.tuple2 tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1706 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1706 with
        | (u,ctx_uvar,g_u) ->
            let uu____1740 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1740
              (fun uu____1749  ->
                 let uu____1750 =
                   let uu____1755 =
                     let uu____1756 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1756  in
                   (u, uu____1755)  in
                 ret uu____1750)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1774 = FStar_Syntax_Util.un_squash t  in
    match uu____1774 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1784 =
          let uu____1785 = FStar_Syntax_Subst.compress t'  in
          uu____1785.FStar_Syntax_Syntax.n  in
        (match uu____1784 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1789 -> false)
    | uu____1790 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1800 = FStar_Syntax_Util.un_squash t  in
    match uu____1800 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1810 =
          let uu____1811 = FStar_Syntax_Subst.compress t'  in
          uu____1811.FStar_Syntax_Syntax.n  in
        (match uu____1810 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1815 -> false)
    | uu____1816 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1827  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1838 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1838 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1845 = goal_to_string hd1  in
                    let uu____1846 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1845 uu____1846);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1853  ->
    let uu____1856 =
      let uu____1859 = cur_goal ()  in
      bind uu____1859
        (fun g  ->
           (let uu____1866 =
              let uu____1867 = FStar_Tactics_Types.goal_type g  in
              uu____1867.FStar_Syntax_Syntax.pos  in
            let uu____1870 =
              let uu____1875 =
                let uu____1876 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1876
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1875)  in
            FStar_Errors.log_issue uu____1866 uu____1870);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1856
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1887  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___105_1897 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___105_1897.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___105_1897.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___105_1897.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___105_1897.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___105_1897.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___105_1897.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___105_1897.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___105_1897.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___105_1897.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___105_1897.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1898 = set ps1  in
         bind uu____1898
           (fun uu____1903  ->
              let uu____1904 = FStar_BigInt.of_int_fs n1  in ret uu____1904))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1911  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1919 = FStar_BigInt.of_int_fs n1  in ret uu____1919)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1932  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1940 = FStar_BigInt.of_int_fs n1  in ret uu____1940)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1953  ->
    let uu____1956 = cur_goal ()  in
    bind uu____1956 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ =
            let uu____1988 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1988 phi  in
          let uu____1989 = new_uvar reason env typ  in
          bind uu____1989
            (fun uu____2004  ->
               match uu____2004 with
               | (uu____2011,ctx_uvar) ->
                   let goal =
                     FStar_Tactics_Types.mk_goal env ctx_uvar opts false  in
                   ret goal)
  
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Reflection_Data.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____2056  ->
                let uu____2057 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2057)
             (fun uu____2060  ->
                let e1 =
                  let uu___106_2062 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___106_2062.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___106_2062.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___106_2062.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___106_2062.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___106_2062.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___106_2062.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___106_2062.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___106_2062.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___106_2062.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___106_2062.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___106_2062.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___106_2062.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___106_2062.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___106_2062.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___106_2062.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___106_2062.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___106_2062.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___106_2062.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___106_2062.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___106_2062.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___106_2062.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___106_2062.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___106_2062.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___106_2062.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___106_2062.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___106_2062.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___106_2062.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___106_2062.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___106_2062.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___106_2062.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___106_2062.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___106_2062.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___106_2062.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___106_2062.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___106_2062.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___106_2062.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___106_2062.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___106_2062.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2082 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2082
                with
                | FStar_Errors.Err (uu____2109,msg) ->
                    let uu____2111 = tts e1 t  in
                    let uu____2112 =
                      let uu____2113 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2113
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2111 uu____2112 msg
                | FStar_Errors.Error (uu____2120,msg,uu____2122) ->
                    let uu____2123 = tts e1 t  in
                    let uu____2124 =
                      let uu____2125 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2125
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2123 uu____2124 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac;
        FStar_TypeChecker_Normalize.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____2152  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___109_2170 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___109_2170.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___109_2170.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___109_2170.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___109_2170.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___109_2170.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___109_2170.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___109_2170.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___109_2170.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___109_2170.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___109_2170.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2194 = get_guard_policy ()  in
      bind uu____2194
        (fun old_pol  ->
           let uu____2200 = set_guard_policy pol  in
           bind uu____2200
             (fun uu____2204  ->
                bind t
                  (fun r  ->
                     let uu____2208 = set_guard_policy old_pol  in
                     bind uu____2208 (fun uu____2212  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2237 =
            let uu____2238 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2238.FStar_TypeChecker_Env.guard_f  in
          match uu____2237 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2242 = istrivial e f  in
              if uu____2242
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2250 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2250
                           (fun goal  ->
                              let goal1 =
                                let uu___110_2257 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___110_2257.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___110_2257.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___110_2257.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2258 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2258
                           (fun goal  ->
                              let goal1 =
                                let uu___111_2265 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___111_2265.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___111_2265.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___111_2265.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2273 =
                              let uu____2274 =
                                let uu____2275 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2275
                                 in
                              Prims.op_Negation uu____2274  in
                            if uu____2273
                            then
                              mlog
                                (fun uu____2280  ->
                                   let uu____2281 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2281)
                                (fun uu____2283  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2290 ->
                              mlog
                                (fun uu____2293  ->
                                   let uu____2294 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2294)
                                (fun uu____2296  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2306 =
      let uu____2309 = cur_goal ()  in
      bind uu____2309
        (fun goal  ->
           let uu____2315 =
             let uu____2324 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2324 t  in
           bind uu____2315
             (fun uu____2336  ->
                match uu____2336 with
                | (t1,typ,guard) ->
                    let uu____2348 =
                      let uu____2351 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2351 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2348 (fun uu____2353  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2306
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2382 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2382 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2393  ->
    let uu____2396 = cur_goal ()  in
    bind uu____2396
      (fun goal  ->
         let uu____2402 =
           let uu____2403 = FStar_Tactics_Types.goal_env goal  in
           let uu____2404 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2403 uu____2404  in
         if uu____2402
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2408 =
              let uu____2409 = FStar_Tactics_Types.goal_env goal  in
              let uu____2410 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2409 uu____2410  in
            fail1 "Not a trivial goal: %s" uu____2408))
  
let (goal_from_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2439 =
            let uu____2440 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2440.FStar_TypeChecker_Env.guard_f  in
          match uu____2439 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2448 = istrivial e f  in
              if uu____2448
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2456 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2456
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___114_2466 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___114_2466.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___114_2466.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___114_2466.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2473  ->
    let uu____2476 = cur_goal ()  in
    bind uu____2476
      (fun g  ->
         let uu____2482 = is_irrelevant g  in
         if uu____2482
         then bind __dismiss (fun uu____2486  -> add_smt_goals [g])
         else
           (let uu____2488 =
              let uu____2489 = FStar_Tactics_Types.goal_env g  in
              let uu____2490 = FStar_Tactics_Types.goal_type g  in
              tts uu____2489 uu____2490  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2488))
  
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a tac -> 'b tac -> ('a,'b) FStar_Pervasives_Native.tuple2 tac
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____2539 =
               try
                 let uu____2573 =
                   let uu____2582 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2582 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2573
               with | uu____2604 -> fail "divide: not enough goals"  in
             bind uu____2539
               (fun uu____2631  ->
                  match uu____2631 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___115_2657 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___115_2657.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___115_2657.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___115_2657.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___115_2657.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___115_2657.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___115_2657.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___115_2657.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___115_2657.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___115_2657.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___116_2659 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___116_2659.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___116_2659.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___116_2659.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___116_2659.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___116_2659.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___116_2659.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___116_2659.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___116_2659.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___116_2659.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2660 = set lp  in
                      bind uu____2660
                        (fun uu____2668  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2682 = set rp  in
                                     bind uu____2682
                                       (fun uu____2690  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___117_2706 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___117_2706.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___117_2706.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___117_2706.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___117_2706.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___117_2706.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___117_2706.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___117_2706.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___117_2706.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___117_2706.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2707 = set p'
                                                       in
                                                    bind uu____2707
                                                      (fun uu____2715  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2736 = divide FStar_BigInt.one f idtac  in
    bind uu____2736
      (fun uu____2749  -> match uu____2749 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2786::uu____2787 ->
             let uu____2790 =
               let uu____2799 = map tau  in
               divide FStar_BigInt.one tau uu____2799  in
             bind uu____2790
               (fun uu____2817  ->
                  match uu____2817 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2858 =
        bind t1
          (fun uu____2863  ->
             let uu____2864 = map t2  in
             bind uu____2864 (fun uu____2872  -> ret ()))
         in
      focus uu____2858
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2881  ->
    let uu____2884 =
      let uu____2887 = cur_goal ()  in
      bind uu____2887
        (fun goal  ->
           let uu____2896 =
             let uu____2903 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2903  in
           match uu____2896 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2912 =
                 let uu____2913 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2913  in
               if uu____2912
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2918 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2918 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2928 = new_uvar "intro" env' typ'  in
                  bind uu____2928
                    (fun uu____2944  ->
                       match uu____2944 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____2964 = set_solution goal sol  in
                           bind uu____2964
                             (fun uu____2970  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____2972 =
                                  let uu____2975 = bnorm_goal g  in
                                  replace_cur uu____2975  in
                                bind uu____2972 (fun uu____2977  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____2982 =
                 let uu____2983 = FStar_Tactics_Types.goal_env goal  in
                 let uu____2984 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____2983 uu____2984  in
               fail1 "goal is not an arrow (%s)" uu____2982)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2884
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2999  ->
    let uu____3006 = cur_goal ()  in
    bind uu____3006
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3023 =
            let uu____3030 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3030  in
          match uu____3023 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3043 =
                let uu____3044 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3044  in
              if uu____3043
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3057 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3057
                    in
                 let bs =
                   let uu____3065 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3065; b]  in
                 let env' =
                   let uu____3083 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3083 bs  in
                 let uu____3084 =
                   let uu____3091 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3091  in
                 bind uu____3084
                   (fun uu____3110  ->
                      match uu____3110 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3124 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3127 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3124
                              FStar_Parser_Const.effect_Tot_lid uu____3127 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3141 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3141 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3163 =
                                   let uu____3164 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3164.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3163
                                  in
                               let uu____3177 = set_solution goal tm  in
                               bind uu____3177
                                 (fun uu____3186  ->
                                    let uu____3187 =
                                      let uu____3190 =
                                        bnorm_goal
                                          (let uu___120_3193 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___120_3193.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___120_3193.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___120_3193.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3190  in
                                    bind uu____3187
                                      (fun uu____3200  ->
                                         let uu____3201 =
                                           let uu____3206 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3206, b)  in
                                         ret uu____3201)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3215 =
                let uu____3216 = FStar_Tactics_Types.goal_env goal  in
                let uu____3217 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3216 uu____3217  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3215))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3235 = cur_goal ()  in
    bind uu____3235
      (fun goal  ->
         mlog
           (fun uu____3242  ->
              let uu____3243 =
                let uu____3244 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3244  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3243)
           (fun uu____3249  ->
              let steps =
                let uu____3253 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3253
                 in
              let t =
                let uu____3257 = FStar_Tactics_Types.goal_env goal  in
                let uu____3258 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3257 uu____3258  in
              let uu____3259 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3259))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3283 =
          mlog
            (fun uu____3288  ->
               let uu____3289 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3289)
            (fun uu____3291  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3297 -> g.FStar_Tactics_Types.opts
                      | uu____3300 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3305  ->
                         let uu____3306 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3306)
                      (fun uu____3309  ->
                         let uu____3310 = __tc e t  in
                         bind uu____3310
                           (fun uu____3331  ->
                              match uu____3331 with
                              | (t1,uu____3341,uu____3342) ->
                                  let steps =
                                    let uu____3346 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3346
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3283
  
let (refine_intro : unit -> unit tac) =
  fun uu____3360  ->
    let uu____3363 =
      let uu____3366 = cur_goal ()  in
      bind uu____3366
        (fun g  ->
           let uu____3373 =
             let uu____3384 = FStar_Tactics_Types.goal_env g  in
             let uu____3385 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3384 uu____3385
              in
           match uu____3373 with
           | (uu____3388,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3413 =
                 let uu____3418 =
                   let uu____3423 =
                     let uu____3424 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3424]  in
                   FStar_Syntax_Subst.open_term uu____3423 phi  in
                 match uu____3418 with
                 | (bvs,phi1) ->
                     let uu____3443 =
                       let uu____3444 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3444  in
                     (uu____3443, phi1)
                  in
               (match uu____3413 with
                | (bv1,phi1) ->
                    let uu____3457 =
                      let uu____3460 = FStar_Tactics_Types.goal_env g  in
                      let uu____3461 =
                        let uu____3462 =
                          let uu____3465 =
                            let uu____3466 =
                              let uu____3473 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3473)  in
                            FStar_Syntax_Syntax.NT uu____3466  in
                          [uu____3465]  in
                        FStar_Syntax_Subst.subst uu____3462 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3460
                        uu____3461 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3457
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3481  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3363
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3500 = cur_goal ()  in
      bind uu____3500
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3508 = FStar_Tactics_Types.goal_env goal  in
               let uu____3509 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3508 uu____3509
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3511 = __tc env t  in
           bind uu____3511
             (fun uu____3530  ->
                match uu____3530 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3545  ->
                         let uu____3546 =
                           let uu____3547 = FStar_Tactics_Types.goal_env goal
                              in
                           tts uu____3547 typ  in
                         let uu____3548 =
                           let uu____3549 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3549
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3546 uu____3548)
                      (fun uu____3552  ->
                         let uu____3553 =
                           let uu____3556 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3556 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3553
                           (fun uu____3558  ->
                              mlog
                                (fun uu____3562  ->
                                   let uu____3563 =
                                     let uu____3564 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     tts uu____3564 typ  in
                                   let uu____3565 =
                                     let uu____3566 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3567 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     tts uu____3566 uu____3567  in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3563 uu____3565)
                                (fun uu____3570  ->
                                   let uu____3571 =
                                     let uu____3574 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3575 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3574 typ uu____3575  in
                                   bind uu____3571
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3581 =
                                             let uu____3582 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3582 t1  in
                                           let uu____3583 =
                                             let uu____3584 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3584 typ  in
                                           let uu____3585 =
                                             let uu____3586 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3587 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3586 uu____3587  in
                                           let uu____3588 =
                                             let uu____3589 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3590 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3589 uu____3590  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3581 uu____3583 uu____3585
                                             uu____3588)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3605 =
        mlog
          (fun uu____3610  ->
             let uu____3611 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3611)
          (fun uu____3614  ->
             let uu____3615 =
               let uu____3622 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3622  in
             bind uu____3615
               (fun uu___88_3631  ->
                  match uu___88_3631 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3640 =
                        let uu____3647 =
                          let uu____3650 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3650
                            (fun uu____3655  ->
                               let uu____3656 = refine_intro ()  in
                               bind uu____3656
                                 (fun uu____3660  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3647  in
                      bind uu____3640
                        (fun uu___87_3667  ->
                           match uu___87_3667 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3675 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3605
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3704 =
             let uu____3707 =
               let uu____3710 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3710  in
             FStar_Util.set_elements uu____3707  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3704
            in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
  
let (uvar_free :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool) =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3788 = f x  in
          bind uu____3788
            (fun y  ->
               let uu____3796 = mapM f xs  in
               bind uu____3796 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3816 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3836 = cur_goal ()  in
        bind uu____3836
          (fun goal  ->
             mlog
               (fun uu____3843  ->
                  let uu____3844 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3844)
               (fun uu____3847  ->
                  let uu____3848 =
                    let uu____3853 =
                      let uu____3856 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3856  in
                    trytac_exn uu____3853  in
                  bind uu____3848
                    (fun uu___89_3863  ->
                       match uu___89_3863 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3871  ->
                                let uu____3872 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3872)
                             (fun uu____3875  ->
                                let uu____3876 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3876 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3900  ->
                                         let uu____3901 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3901)
                                      (fun uu____3904  ->
                                         let uu____3905 =
                                           let uu____3906 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3906  in
                                         if uu____3905
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3910 =
                                              let uu____3917 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3917
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3910
                                              (fun uu____3928  ->
                                                 match uu____3928 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____3955 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____3955
                                                        in
                                                     let uu____3958 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____3958
                                                       (fun uu____3966  ->
                                                          let u1 =
                                                            let uu____3968 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____3968
                                                              u
                                                             in
                                                          let uu____3969 =
                                                            let uu____3970 =
                                                              let uu____3973
                                                                =
                                                                let uu____3974
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____3974
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____3973
                                                               in
                                                            uu____3970.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____3969
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4002)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4026
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4026
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    (let uu____4030
                                                                    =
                                                                    let uu____4033
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___121_4036
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___121_4036.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___121_4036.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })  in
                                                                    [uu____4033]
                                                                     in
                                                                    add_goals
                                                                    uu____4030))
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4091 =
        mlog
          (fun uu____4096  ->
             let uu____4097 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4097)
          (fun uu____4100  ->
             let uu____4101 = cur_goal ()  in
             bind uu____4101
               (fun goal  ->
                  let uu____4107 =
                    let uu____4116 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4116 tm  in
                  bind uu____4107
                    (fun uu____4130  ->
                       match uu____4130 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4143 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4143 typ  in
                           let uu____4144 =
                             let uu____4147 =
                               let uu____4150 = __apply uopt tm1 typ1  in
                               bind uu____4150
                                 (fun uu____4155  ->
                                    let uu____4156 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4156 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4147  in
                           let uu____4157 =
                             let uu____4160 =
                               let uu____4161 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4161 tm1  in
                             let uu____4162 =
                               let uu____4163 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4163 typ1  in
                             let uu____4164 =
                               let uu____4165 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4166 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4165 uu____4166  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4160 uu____4162 uu____4164
                              in
                           try_unif uu____4144 uu____4157)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4091
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4189 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4189
    then
      let uu____4196 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4215 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4256 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4196 with
      | (pre,post) ->
          let post1 =
            let uu____4292 =
              let uu____4301 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4301]  in
            FStar_Syntax_Util.mk_app post uu____4292  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4325 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4325
       then
         let uu____4332 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4332
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4365 =
      let uu____4368 =
        mlog
          (fun uu____4373  ->
             let uu____4374 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4374)
          (fun uu____4378  ->
             let is_unit_t t =
               let uu____4385 =
                 let uu____4386 = FStar_Syntax_Subst.compress t  in
                 uu____4386.FStar_Syntax_Syntax.n  in
               match uu____4385 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4390 -> false  in
             let uu____4391 = cur_goal ()  in
             bind uu____4391
               (fun goal  ->
                  let uu____4397 =
                    let uu____4406 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4406 tm  in
                  bind uu____4397
                    (fun uu____4421  ->
                       match uu____4421 with
                       | (tm1,t,guard) ->
                           let uu____4433 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4433 with
                            | (bs,comp) ->
                                let uu____4460 = lemma_or_sq comp  in
                                (match uu____4460 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4479 =
                                       FStar_List.fold_left
                                         (fun uu____4521  ->
                                            fun uu____4522  ->
                                              match (uu____4521, uu____4522)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4613 =
                                                    is_unit_t b_t  in
                                                  if uu____4613
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4649 =
                                                       let uu____4662 =
                                                         let uu____4663 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4663.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4666 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4662
                                                         uu____4666 b_t
                                                        in
                                                     match uu____4649 with
                                                     | (u,uu____4682,g_u) ->
                                                         let uu____4696 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4696,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4479 with
                                      | (uvs,implicits,subst1) ->
                                          let uvs1 = FStar_List.rev uvs  in
                                          let pre1 =
                                            FStar_Syntax_Subst.subst subst1
                                              pre
                                             in
                                          let post1 =
                                            FStar_Syntax_Subst.subst subst1
                                              post
                                             in
                                          let uu____4757 =
                                            let uu____4760 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4761 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4762 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4760 uu____4761
                                              uu____4762
                                             in
                                          bind uu____4757
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4770 =
                                                   let uu____4771 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4771 tm1  in
                                                 let uu____4772 =
                                                   let uu____4773 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4774 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4773 uu____4774
                                                    in
                                                 let uu____4775 =
                                                   let uu____4776 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4777 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4776 uu____4777
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4770 uu____4772
                                                   uu____4775
                                               else
                                                 (let uu____4779 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4779
                                                    (fun uu____4784  ->
                                                       let uu____4785 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4785
                                                         (fun uu____4793  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4818
                                                                  =
                                                                  let uu____4821
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4821
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4818
                                                                 in
                                                              FStar_List.existsML
                                                                (fun u  ->
                                                                   FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                free_uvars
                                                               in
                                                            let appears uv
                                                              goals =
                                                              FStar_List.existsML
                                                                (fun g'  ->
                                                                   let uu____4856
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4856)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4872
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4872
                                                              with
                                                              | (hd1,uu____4888)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4910)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4931
                                                                    -> false)
                                                               in
                                                            let uu____4932 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4995
                                                                     ->
                                                                    match uu____4995
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5018
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5018
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5044)
                                                                    ->
                                                                    let uu____5065
                                                                    =
                                                                    let uu____5066
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5066.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5065
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5080)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___124_5104
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___124_5104.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___124_5104.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___124_5104.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5117
                                                                    ->
                                                                    let env =
                                                                    let uu___125_5119
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___125_5119.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5121
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5121
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____5124
                                                                    =
                                                                    let uu____5131
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5131
                                                                    term1  in
                                                                    match uu____5124
                                                                    with
                                                                    | 
                                                                    (uu____5132,uu____5133,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5135
                                                                    =
                                                                    let uu____5140
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5140
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5135
                                                                    (fun
                                                                    uu___90_5152
                                                                     ->
                                                                    match uu___90_5152
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    ret
                                                                    ([], [])
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g ->
                                                                    ret
                                                                    ([], [g]))))))
                                                               in
                                                            bind uu____4932
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5220
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5220
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5242
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5242
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5303
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5303
                                                                    then
                                                                    let uu____5306
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5306
                                                                    else
                                                                    filter' f
                                                                    xs1
                                                                    in
                                                                 let sub_goals1
                                                                   =
                                                                   filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5320
                                                                    =
                                                                    let uu____5321
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5321
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5320)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5322
                                                                   =
                                                                   let uu____5325
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5325
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5322
                                                                   (fun
                                                                    uu____5328
                                                                     ->
                                                                    let uu____5329
                                                                    =
                                                                    let uu____5332
                                                                    =
                                                                    let uu____5333
                                                                    =
                                                                    let uu____5334
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5335
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5334
                                                                    uu____5335
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5333
                                                                     in
                                                                    if
                                                                    uu____5332
                                                                    then
                                                                    let uu____5338
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5338
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5329
                                                                    (fun
                                                                    uu____5342
                                                                     ->
                                                                    let uu____5343
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5343
                                                                    (fun
                                                                    uu____5347
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4368  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4365
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5369 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5369 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5379::(e1,uu____5381)::(e2,uu____5383)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5426 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5450 = destruct_eq' typ  in
    match uu____5450 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5480 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5480 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env,FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____5542 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5542 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5590 = aux e'  in
               FStar_Util.map_opt uu____5590
                 (fun uu____5614  ->
                    match uu____5614 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5635 = aux e  in
      FStar_Util.map_opt uu____5635
        (fun uu____5659  ->
           match uu____5659 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_left
        (fun e1  -> fun b  -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
  
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option)
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let uu____5726 =
            let uu____5735 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5735  in
          FStar_Util.map_opt uu____5726
            (fun uu____5750  ->
               match uu____5750 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___126_5769 = bv  in
                     let uu____5770 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___126_5769.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___126_5769.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5770
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___127_5778 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5779 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5786 =
                       let uu____5789 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5789  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___127_5778.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5779;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5786;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___127_5778.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___127_5778.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___127_5778.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___128_5790 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___128_5790.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___128_5790.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___128_5790.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5800 = cur_goal ()  in
    bind uu____5800
      (fun goal  ->
         let uu____5808 = h  in
         match uu____5808 with
         | (bv,uu____5812) ->
             mlog
               (fun uu____5816  ->
                  let uu____5817 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5818 =
                    let uu____5819 = FStar_Tactics_Types.goal_env goal  in
                    tts uu____5819 bv.FStar_Syntax_Syntax.sort  in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5817
                    uu____5818)
               (fun uu____5822  ->
                  let uu____5823 =
                    let uu____5832 = FStar_Tactics_Types.goal_env goal  in
                    split_env bv uu____5832  in
                  match uu____5823 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5853 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5853 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5868 =
                             let uu____5869 = FStar_Syntax_Subst.compress x
                                in
                             uu____5869.FStar_Syntax_Syntax.n  in
                           (match uu____5868 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___129_5886 = bv1  in
                                  let uu____5887 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___129_5886.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___129_5886.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5887
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let new_env = push_bvs e0 (bv :: bvs1)  in
                                let new_goal =
                                  let uu___130_5895 =
                                    goal.FStar_Tactics_Types.goal_ctx_uvar
                                     in
                                  let uu____5896 =
                                    FStar_TypeChecker_Env.all_binders new_env
                                     in
                                  let uu____5903 =
                                    let uu____5906 =
                                      FStar_Tactics_Types.goal_type goal  in
                                    FStar_Syntax_Subst.subst s uu____5906  in
                                  {
                                    FStar_Syntax_Syntax.ctx_uvar_head =
                                      (uu___130_5895.FStar_Syntax_Syntax.ctx_uvar_head);
                                    FStar_Syntax_Syntax.ctx_uvar_gamma =
                                      (new_env.FStar_TypeChecker_Env.gamma);
                                    FStar_Syntax_Syntax.ctx_uvar_binders =
                                      uu____5896;
                                    FStar_Syntax_Syntax.ctx_uvar_typ =
                                      uu____5903;
                                    FStar_Syntax_Syntax.ctx_uvar_reason =
                                      (uu___130_5895.FStar_Syntax_Syntax.ctx_uvar_reason);
                                    FStar_Syntax_Syntax.ctx_uvar_should_check
                                      =
                                      (uu___130_5895.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                    FStar_Syntax_Syntax.ctx_uvar_range =
                                      (uu___130_5895.FStar_Syntax_Syntax.ctx_uvar_range)
                                  }  in
                                replace_cur
                                  (let uu___131_5909 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___131_5909.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       new_goal;
                                     FStar_Tactics_Types.opts =
                                       (uu___131_5909.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___131_5909.FStar_Tactics_Types.is_guard)
                                   })
                            | uu____5910 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5911 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5932 = cur_goal ()  in
      bind uu____5932
        (fun goal  ->
           let uu____5943 = b  in
           match uu____5943 with
           | (bv,uu____5947) ->
               let bv' =
                 let uu____5949 =
                   let uu___132_5950 = bv  in
                   let uu____5951 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5951;
                     FStar_Syntax_Syntax.index =
                       (uu___132_5950.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___132_5950.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5949  in
               let s1 =
                 let uu____5955 =
                   let uu____5956 =
                     let uu____5963 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5963)  in
                   FStar_Syntax_Syntax.NT uu____5956  in
                 [uu____5955]  in
               let uu____5968 = subst_goal bv bv' s1 goal  in
               (match uu____5968 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5983 = cur_goal ()  in
    bind uu____5983
      (fun goal  ->
         let uu____5992 = b  in
         match uu____5992 with
         | (bv,uu____5996) ->
             let uu____5997 =
               let uu____6006 = FStar_Tactics_Types.goal_env goal  in
               split_env bv uu____6006  in
             (match uu____5997 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____6027 = FStar_Syntax_Util.type_u ()  in
                  (match uu____6027 with
                   | (ty,u) ->
                       let uu____6036 = new_uvar "binder_retype" e0 ty  in
                       bind uu____6036
                         (fun uu____6054  ->
                            match uu____6054 with
                            | (t',u_t') ->
                                let bv'' =
                                  let uu___133_6064 = bv  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___133_6064.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___133_6064.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t'
                                  }  in
                                let s =
                                  let uu____6068 =
                                    let uu____6069 =
                                      let uu____6076 =
                                        FStar_Syntax_Syntax.bv_to_name bv''
                                         in
                                      (bv, uu____6076)  in
                                    FStar_Syntax_Syntax.NT uu____6069  in
                                  [uu____6068]  in
                                let bvs1 =
                                  FStar_List.map
                                    (fun b1  ->
                                       let uu___134_6088 = b1  in
                                       let uu____6089 =
                                         FStar_Syntax_Subst.subst s
                                           b1.FStar_Syntax_Syntax.sort
                                          in
                                       {
                                         FStar_Syntax_Syntax.ppname =
                                           (uu___134_6088.FStar_Syntax_Syntax.ppname);
                                         FStar_Syntax_Syntax.index =
                                           (uu___134_6088.FStar_Syntax_Syntax.index);
                                         FStar_Syntax_Syntax.sort =
                                           uu____6089
                                       }) bvs
                                   in
                                let env' = push_bvs e0 (bv'' :: bvs1)  in
                                bind __dismiss
                                  (fun uu____6096  ->
                                     let new_goal =
                                       let uu____6098 =
                                         FStar_Tactics_Types.goal_with_env
                                           goal env'
                                          in
                                       let uu____6099 =
                                         let uu____6100 =
                                           FStar_Tactics_Types.goal_type goal
                                            in
                                         FStar_Syntax_Subst.subst s
                                           uu____6100
                                          in
                                       FStar_Tactics_Types.goal_with_type
                                         uu____6098 uu____6099
                                        in
                                     let uu____6101 = add_goals [new_goal]
                                        in
                                     bind uu____6101
                                       (fun uu____6106  ->
                                          let uu____6107 =
                                            FStar_Syntax_Util.mk_eq2
                                              (FStar_Syntax_Syntax.U_succ u)
                                              ty bv.FStar_Syntax_Syntax.sort
                                              t'
                                             in
                                          add_irrelevant_goal
                                            "binder_retype equation" e0
                                            uu____6107
                                            goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6126 = cur_goal ()  in
      bind uu____6126
        (fun goal  ->
           let uu____6135 = b  in
           match uu____6135 with
           | (bv,uu____6139) ->
               let uu____6140 =
                 let uu____6149 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6149  in
               (match uu____6140 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____6173 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____6173
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___135_6178 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___135_6178.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___135_6178.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    let uu____6180 =
                      FStar_Tactics_Types.goal_with_env goal env'  in
                    replace_cur uu____6180))
  
let (revert : unit -> unit tac) =
  fun uu____6187  ->
    let uu____6190 = cur_goal ()  in
    bind uu____6190
      (fun goal  ->
         let uu____6196 =
           let uu____6203 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6203  in
         match uu____6196 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6219 =
                 let uu____6222 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6222  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6219
                in
             let uu____6231 = new_uvar "revert" env' typ'  in
             bind uu____6231
               (fun uu____6246  ->
                  match uu____6246 with
                  | (r,u_r) ->
                      let uu____6255 =
                        let uu____6258 =
                          let uu____6259 =
                            let uu____6260 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6260.FStar_Syntax_Syntax.pos  in
                          let uu____6263 =
                            let uu____6268 =
                              let uu____6269 =
                                let uu____6276 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6276  in
                              [uu____6269]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6268  in
                          uu____6263 FStar_Pervasives_Native.None uu____6259
                           in
                        set_solution goal uu____6258  in
                      bind uu____6255
                        (fun uu____6293  ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                              in
                           replace_cur g)))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____6305 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6305
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6318 = cur_goal ()  in
    bind uu____6318
      (fun goal  ->
         mlog
           (fun uu____6326  ->
              let uu____6327 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6328 =
                let uu____6329 =
                  let uu____6330 =
                    let uu____6337 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6337  in
                  FStar_All.pipe_right uu____6330 FStar_List.length  in
                FStar_All.pipe_right uu____6329 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6327 uu____6328)
           (fun uu____6350  ->
              let uu____6351 =
                let uu____6360 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6360  in
              match uu____6351 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6399 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6399
                        then
                          let uu____6402 =
                            let uu____6403 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6403
                             in
                          fail uu____6402
                        else check1 bvs2
                     in
                  let uu____6405 =
                    let uu____6406 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6406  in
                  if uu____6405
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6410 = check1 bvs  in
                     bind uu____6410
                       (fun uu____6416  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6418 =
                            let uu____6425 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6425  in
                          bind uu____6418
                            (fun uu____6434  ->
                               match uu____6434 with
                               | (ut,uvar_ut) ->
                                   let uu____6443 = set_solution goal ut  in
                                   bind uu____6443
                                     (fun uu____6448  ->
                                        let uu____6449 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6449))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6456  ->
    let uu____6459 = cur_goal ()  in
    bind uu____6459
      (fun goal  ->
         let uu____6465 =
           let uu____6472 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6472  in
         match uu____6465 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6480) ->
             let uu____6485 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6485)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6495 = cur_goal ()  in
    bind uu____6495
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6505 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6505  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6508  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6518 = cur_goal ()  in
    bind uu____6518
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6528 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6528  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6531  -> add_goals [g']))
  
let rec (tac_fold_env :
  FStar_Tactics_Types.direction ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun d  ->
    fun f  ->
      fun env  ->
        fun t  ->
          let tn =
            let uu____6571 = FStar_Syntax_Subst.compress t  in
            uu____6571.FStar_Syntax_Syntax.n  in
          let uu____6574 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___139_6580 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___139_6580.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___139_6580.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6574
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6596 =
                   let uu____6597 = FStar_Syntax_Subst.compress t1  in
                   uu____6597.FStar_Syntax_Syntax.n  in
                 match uu____6596 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6624 = ff hd1  in
                     bind uu____6624
                       (fun hd2  ->
                          let fa uu____6646 =
                            match uu____6646 with
                            | (a,q) ->
                                let uu____6659 = ff a  in
                                bind uu____6659 (fun a1  -> ret (a1, q))
                             in
                          let uu____6672 = mapM fa args  in
                          bind uu____6672
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6738 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6738 with
                      | (bs1,t') ->
                          let uu____6747 =
                            let uu____6750 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6750 t'  in
                          bind uu____6747
                            (fun t''  ->
                               let uu____6754 =
                                 let uu____6755 =
                                   let uu____6772 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6779 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6772, uu____6779, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6755  in
                               ret uu____6754))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6848 = ff hd1  in
                     bind uu____6848
                       (fun hd2  ->
                          let ffb br =
                            let uu____6863 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6863 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6895 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6895  in
                                let uu____6896 = ff1 e  in
                                bind uu____6896
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6911 = mapM ffb brs  in
                          bind uu____6911
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6955;
                          FStar_Syntax_Syntax.lbtyp = uu____6956;
                          FStar_Syntax_Syntax.lbeff = uu____6957;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6959;
                          FStar_Syntax_Syntax.lbpos = uu____6960;_}::[]),e)
                     ->
                     let lb =
                       let uu____6985 =
                         let uu____6986 = FStar_Syntax_Subst.compress t1  in
                         uu____6986.FStar_Syntax_Syntax.n  in
                       match uu____6985 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6990) -> lb
                       | uu____7003 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7012 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7012
                         (fun def1  ->
                            ret
                              (let uu___136_7018 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___136_7018.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___136_7018.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___136_7018.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___136_7018.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___136_7018.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___136_7018.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7019 = fflb lb  in
                     bind uu____7019
                       (fun lb1  ->
                          let uu____7029 =
                            let uu____7034 =
                              let uu____7035 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7035]  in
                            FStar_Syntax_Subst.open_term uu____7034 e  in
                          match uu____7029 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7059 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7059  in
                              let uu____7060 = ff1 e1  in
                              bind uu____7060
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7101 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7101
                         (fun def  ->
                            ret
                              (let uu___137_7107 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___137_7107.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___137_7107.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___137_7107.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___137_7107.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___137_7107.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___137_7107.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7108 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7108 with
                      | (lbs1,e1) ->
                          let uu____7123 = mapM fflb lbs1  in
                          bind uu____7123
                            (fun lbs2  ->
                               let uu____7135 = ff e1  in
                               bind uu____7135
                                 (fun e2  ->
                                    let uu____7143 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7143 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7211 = ff t2  in
                     bind uu____7211
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7242 = ff t2  in
                     bind uu____7242
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7249 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___138_7256 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___138_7256.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___138_7256.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let (pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____7293 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7293 with
            | (t1,lcomp,g) ->
                let uu____7305 =
                  (let uu____7308 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7308) ||
                    (let uu____7310 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7310)
                   in
                if uu____7305
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7320 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7320
                       (fun uu____7336  ->
                          match uu____7336 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7349  ->
                                    let uu____7350 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7351 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7350 uu____7351);
                               (let uu____7352 =
                                  let uu____7355 =
                                    let uu____7356 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7356 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7355
                                    opts
                                   in
                                bind uu____7352
                                  (fun uu____7359  ->
                                     let uu____7360 =
                                       bind tau
                                         (fun uu____7366  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7372  ->
                                                 let uu____7373 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7374 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7373 uu____7374);
                                            ret ut1)
                                        in
                                     focus uu____7360))))
                      in
                   let uu____7375 = trytac' rewrite_eq  in
                   bind uu____7375
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
  
type ctrl = FStar_BigInt.t[@@deriving show]
let (keepGoing : ctrl) = FStar_BigInt.zero 
let (proceedToNextSubtree : FStar_BigInt.bigint) = FStar_BigInt.one 
let (globalStop : FStar_BigInt.bigint) =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool[@@deriving show]
let (skipThisTerm : Prims.bool) = false 
let (rewroteThisTerm : Prims.bool) = true 
type 'a ctrl_tac = ('a,ctrl) FStar_Pervasives_Native.tuple2 tac[@@deriving
                                                                 show]
let rec (ctrl_tac_fold :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun f  ->
    fun env  ->
      fun ctrl  ->
        fun t  ->
          let keep_going c =
            if c = proceedToNextSubtree then keepGoing else c  in
          let maybe_continue ctrl1 t1 k =
            if ctrl1 = globalStop
            then ret (t1, globalStop)
            else
              if ctrl1 = proceedToNextSubtree
              then ret (t1, keepGoing)
              else k t1
             in
          let uu____7573 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7573
            (fun t1  ->
               let uu____7581 =
                 f env
                   (let uu___142_7590 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___142_7590.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___142_7590.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7581
                 (fun uu____7606  ->
                    match uu____7606 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7629 =
                               let uu____7630 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7630.FStar_Syntax_Syntax.n  in
                             match uu____7629 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7663 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7663
                                   (fun uu____7688  ->
                                      match uu____7688 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7704 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7704
                                            (fun uu____7731  ->
                                               match uu____7731 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___140_7761 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___140_7761.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___140_7761.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7797 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7797 with
                                  | (bs1,t') ->
                                      let uu____7812 =
                                        let uu____7819 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7819 ctrl1 t'
                                         in
                                      bind uu____7812
                                        (fun uu____7837  ->
                                           match uu____7837 with
                                           | (t'',ctrl2) ->
                                               let uu____7852 =
                                                 let uu____7859 =
                                                   let uu___141_7862 = t4  in
                                                   let uu____7865 =
                                                     let uu____7866 =
                                                       let uu____7883 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7890 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7883,
                                                         uu____7890, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7866
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7865;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___141_7862.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___141_7862.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7859, ctrl2)  in
                                               ret uu____7852))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7937 -> ret (t3, ctrl1))))

and (ctrl_tac_fold_args :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl ->
        FStar_Syntax_Syntax.arg Prims.list ->
          FStar_Syntax_Syntax.arg Prims.list ctrl_tac)
  =
  fun f  ->
    fun env  ->
      fun ctrl  ->
        fun ts  ->
          match ts with
          | [] -> ret ([], ctrl)
          | (t,q)::ts1 ->
              let uu____7980 = ctrl_tac_fold f env ctrl t  in
              bind uu____7980
                (fun uu____8004  ->
                   match uu____8004 with
                   | (t1,ctrl1) ->
                       let uu____8019 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8019
                         (fun uu____8046  ->
                            match uu____8046 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      unit tac ->
        FStar_Options.optionstate ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps  ->
    fun ctrl  ->
      fun rewriter  ->
        fun opts  ->
          fun env  ->
            fun t  ->
              let t1 = FStar_Syntax_Subst.compress t  in
              let uu____8128 =
                let uu____8135 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8135
                  (fun uu____8144  ->
                     let uu____8145 = ctrl t1  in
                     bind uu____8145
                       (fun res  ->
                          let uu____8168 = trivial ()  in
                          bind uu____8168 (fun uu____8176  -> ret res)))
                 in
              bind uu____8128
                (fun uu____8192  ->
                   match uu____8192 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8216 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8216 with
                          | (t2,lcomp,g) ->
                              let uu____8232 =
                                (let uu____8235 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8235) ||
                                  (let uu____8237 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8237)
                                 in
                              if uu____8232
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8252 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8252
                                   (fun uu____8272  ->
                                      match uu____8272 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8289  ->
                                                let uu____8290 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8291 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8290 uu____8291);
                                           (let uu____8292 =
                                              let uu____8295 =
                                                let uu____8296 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8296 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8295 opts
                                               in
                                            bind uu____8292
                                              (fun uu____8303  ->
                                                 let uu____8304 =
                                                   bind rewriter
                                                     (fun uu____8318  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8324  ->
                                                             let uu____8325 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8326 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8325
                                                               uu____8326);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8304)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____8374 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8374 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8411  ->
                     let uu____8412 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____8412);
                bind dismiss_all
                  (fun uu____8415  ->
                     let uu____8416 =
                       let uu____8423 = FStar_Tactics_Types.goal_env g  in
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts) uu____8423 keepGoing
                         gt1
                        in
                     bind uu____8416
                       (fun uu____8435  ->
                          match uu____8435 with
                          | (gt',uu____8443) ->
                              (log ps
                                 (fun uu____8447  ->
                                    let uu____8448 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____8448);
                               (let uu____8449 = push_goals gs  in
                                bind uu____8449
                                  (fun uu____8454  ->
                                     let uu____8455 =
                                       let uu____8458 =
                                         FStar_Tactics_Types.goal_with_type g
                                           gt'
                                          in
                                       [uu____8458]  in
                                     add_goals uu____8455)))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____8484 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8484 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8521  ->
                     let uu____8522 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____8522);
                bind dismiss_all
                  (fun uu____8525  ->
                     let uu____8526 =
                       let uu____8529 = FStar_Tactics_Types.goal_env g  in
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         uu____8529 gt1
                        in
                     bind uu____8526
                       (fun gt'  ->
                          log ps
                            (fun uu____8537  ->
                               let uu____8538 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____8538);
                          (let uu____8539 = push_goals gs  in
                           bind uu____8539
                             (fun uu____8544  ->
                                let uu____8545 =
                                  let uu____8548 =
                                    FStar_Tactics_Types.goal_with_type g gt'
                                     in
                                  [uu____8548]  in
                                add_goals uu____8545))))))
  
let (trefl : unit -> unit tac) =
  fun uu____8555  ->
    let uu____8558 = cur_goal ()  in
    bind uu____8558
      (fun g  ->
         let uu____8576 =
           let uu____8581 = FStar_Tactics_Types.goal_type g  in
           FStar_Syntax_Util.un_squash uu____8581  in
         match uu____8576 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8589 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8589 with
              | (hd1,args) ->
                  let uu____8622 =
                    let uu____8633 =
                      let uu____8634 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8634.FStar_Syntax_Syntax.n  in
                    (uu____8633, args)  in
                  (match uu____8622 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8646::(l,uu____8648)::(r,uu____8650)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8677 =
                         let uu____8680 = FStar_Tactics_Types.goal_env g  in
                         do_unify uu____8680 l r  in
                       bind uu____8677
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8687 =
                                let uu____8688 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8688 l  in
                              let uu____8689 =
                                let uu____8690 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8690 r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8687 uu____8689
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8693) ->
                       let uu____8706 =
                         let uu____8707 = FStar_Tactics_Types.goal_env g  in
                         tts uu____8707 t  in
                       fail1 "trefl: not an equality (%s)" uu____8706))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8716  ->
    let uu____8719 = cur_goal ()  in
    bind uu____8719
      (fun g  ->
         let uu____8725 =
           let uu____8732 = FStar_Tactics_Types.goal_env g  in
           let uu____8733 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8732 uu____8733  in
         bind uu____8725
           (fun uu____8742  ->
              match uu____8742 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___143_8752 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___143_8752.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___143_8752.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___143_8752.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8755  ->
                       let uu____8756 =
                         let uu____8759 = FStar_Tactics_Types.goal_env g  in
                         let uu____8760 =
                           let uu____8761 =
                             let uu____8762 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8763 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8762
                               uu____8763
                              in
                           let uu____8764 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8765 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8761 uu____8764 u
                             uu____8765
                            in
                         add_irrelevant_goal "dup equation" uu____8759
                           uu____8760 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8756
                         (fun uu____8768  ->
                            let uu____8769 = add_goals [g']  in
                            bind uu____8769 (fun uu____8773  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8780  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___144_8797 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___144_8797.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___144_8797.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___144_8797.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___144_8797.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___144_8797.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___144_8797.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___144_8797.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___144_8797.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___144_8797.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___144_8797.FStar_Tactics_Types.freshness)
                })
         | uu____8798 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8807  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___145_8820 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___145_8820.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___145_8820.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___145_8820.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___145_8820.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___145_8820.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___145_8820.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___145_8820.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___145_8820.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___145_8820.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___145_8820.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8827  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8834 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8854 =
      let uu____8861 = cur_goal ()  in
      bind uu____8861
        (fun g  ->
           let uu____8871 =
             let uu____8880 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8880 t  in
           bind uu____8871
             (fun uu____8908  ->
                match uu____8908 with
                | (t1,typ,guard) ->
                    let uu____8924 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8924 with
                     | (hd1,args) ->
                         let uu____8967 =
                           let uu____8980 =
                             let uu____8981 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8981.FStar_Syntax_Syntax.n  in
                           (uu____8980, args)  in
                         (match uu____8967 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9000)::(q,uu____9002)::[]) when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid
                              ->
                              let v_p =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None p
                                 in
                              let v_q =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None q
                                 in
                              let g1 =
                                let uu____9040 =
                                  let uu____9041 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9041
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9040
                                 in
                              let g2 =
                                let uu____9043 =
                                  let uu____9044 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9044
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9043
                                 in
                              bind __dismiss
                                (fun uu____9051  ->
                                   let uu____9052 = add_goals [g1; g2]  in
                                   bind uu____9052
                                     (fun uu____9061  ->
                                        let uu____9062 =
                                          let uu____9067 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9068 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9067, uu____9068)  in
                                        ret uu____9062))
                          | uu____9073 ->
                              let uu____9086 =
                                let uu____9087 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9087 typ  in
                              fail1 "Not a disjunction: %s" uu____9086))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8854
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9117 = cur_goal ()  in
    bind uu____9117
      (fun g  ->
         FStar_Options.push ();
         (let uu____9130 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____9130);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___146_9137 = g  in
                 {
                   FStar_Tactics_Types.goal_main_env =
                     (uu___146_9137.FStar_Tactics_Types.goal_main_env);
                   FStar_Tactics_Types.goal_ctx_uvar =
                     (uu___146_9137.FStar_Tactics_Types.goal_ctx_uvar);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___146_9137.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____9145  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9158  ->
    let uu____9161 = cur_goal ()  in
    bind uu____9161
      (fun g  ->
         let uu____9167 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9167)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9176  ->
    let uu____9179 = cur_goal ()  in
    bind uu____9179
      (fun g  ->
         let uu____9185 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9185)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9194  ->
    let uu____9197 = cur_goal ()  in
    bind uu____9197
      (fun g  ->
         let uu____9203 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9203)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9220 =
        let uu____9223 = cur_goal ()  in
        bind uu____9223
          (fun goal  ->
             let env =
               let uu____9231 = FStar_Tactics_Types.goal_env goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____9231 ty  in
             let uu____9232 = __tc env tm  in
             bind uu____9232
               (fun uu____9252  ->
                  match uu____9252 with
                  | (tm1,typ,guard) ->
                      let uu____9264 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____9264 (fun uu____9268  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9220
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9291 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9297 =
              let uu____9304 =
                let uu____9305 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9305
                 in
              new_uvar "uvar_env.2" env uu____9304  in
            bind uu____9297
              (fun uu____9321  ->
                 match uu____9321 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9291
        (fun typ  ->
           let uu____9333 = new_uvar "uvar_env" env typ  in
           bind uu____9333
             (fun uu____9347  -> match uu____9347 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9365 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9384 -> g.FStar_Tactics_Types.opts
             | uu____9387 -> FStar_Options.peek ()  in
           let uu____9390 = FStar_Syntax_Util.head_and_args t  in
           match uu____9390 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9408);
                FStar_Syntax_Syntax.pos = uu____9409;
                FStar_Syntax_Syntax.vars = uu____9410;_},uu____9411)
               ->
               let env1 =
                 let uu___147_9453 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___147_9453.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___147_9453.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___147_9453.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___147_9453.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___147_9453.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___147_9453.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___147_9453.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___147_9453.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___147_9453.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___147_9453.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___147_9453.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___147_9453.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___147_9453.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___147_9453.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___147_9453.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___147_9453.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___147_9453.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___147_9453.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___147_9453.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___147_9453.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___147_9453.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___147_9453.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___147_9453.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___147_9453.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___147_9453.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___147_9453.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___147_9453.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___147_9453.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___147_9453.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___147_9453.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___147_9453.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___147_9453.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___147_9453.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___147_9453.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___147_9453.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___147_9453.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___147_9453.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___147_9453.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9455 =
                 let uu____9458 = bnorm_goal g  in [uu____9458]  in
               add_goals uu____9455
           | uu____9459 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9365
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  -> do_unify ps.FStar_Tactics_Types.main_context t1 t2)
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____9520  ->
             let uu____9521 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9521
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (fresh_bv_named :
  Prims.string -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.bv tac) =
  fun nm  ->
    fun t  ->
      bind idtac
        (fun uu____9542  ->
           let uu____9543 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9543)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9553 =
      mlog
        (fun uu____9558  ->
           let uu____9559 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9559)
        (fun uu____9562  ->
           let uu____9563 = cur_goal ()  in
           bind uu____9563
             (fun g  ->
                let uu____9569 =
                  let uu____9578 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9578 ty  in
                bind uu____9569
                  (fun uu____9590  ->
                     match uu____9590 with
                     | (ty1,uu____9600,guard) ->
                         let uu____9602 =
                           let uu____9605 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9605 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9602
                           (fun uu____9608  ->
                              let uu____9609 =
                                let uu____9612 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9613 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9612 uu____9613 ty1  in
                              bind uu____9609
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9619 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9619
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                        FStar_TypeChecker_Normalize.Primops;
                                        FStar_TypeChecker_Normalize.Simplify;
                                        FStar_TypeChecker_Normalize.UnfoldTac;
                                        FStar_TypeChecker_Normalize.Unmeta]
                                         in
                                      let ng =
                                        let uu____9625 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9626 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9625 uu____9626
                                         in
                                      let nty =
                                        let uu____9628 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9628 ty1  in
                                      let uu____9629 =
                                        let uu____9632 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9632 ng nty  in
                                      bind uu____9629
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9638 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9638
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9553
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9660::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9688 = init xs  in x :: uu____9688
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9705) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9762 = last args  in
        (match uu____9762 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9784 =
               let uu____9785 =
                 let uu____9790 =
                   let uu____9791 =
                     let uu____9796 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9796  in
                   uu____9791 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9790, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9785  in
             FStar_All.pipe_left ret uu____9784)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9807,uu____9808) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9852 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9852 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9885 =
                    let uu____9886 =
                      let uu____9891 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9891)  in
                    FStar_Reflection_Data.Tv_Abs uu____9886  in
                  FStar_All.pipe_left ret uu____9885))
    | FStar_Syntax_Syntax.Tm_type uu____9894 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9914 ->
        let uu____9927 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9927 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9957 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9957 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9996 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____10004 =
          let uu____10005 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____10005  in
        FStar_All.pipe_left ret uu____10004
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
        let uu____10030 =
          let uu____10031 =
            let uu____10036 =
              let uu____10037 =
                FStar_Syntax_Unionfind.uvar_id
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_BigInt.of_int_fs uu____10037  in
            (uu____10036, (ctx_u, s))  in
          FStar_Reflection_Data.Tv_Uvar uu____10031  in
        FStar_All.pipe_left ret uu____10030
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____10073 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____10078 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____10078 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____10117 ->
                          failwith
                            "impossible: open_term returned different amount of binders"
                       in
                    FStar_All.pipe_left ret
                      (FStar_Reflection_Data.Tv_Let
                         (false, (FStar_Pervasives_Native.fst b1),
                           (lb.FStar_Syntax_Syntax.lbdef), t22))))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____10147 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____10151 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____10151 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____10171 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____10175 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____10229 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____10229
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____10248 =
                let uu____10255 =
                  FStar_List.map
                    (fun uu____10267  ->
                       match uu____10267 with
                       | (p1,uu____10275) -> inspect_pat p1) ps
                   in
                (fv, uu____10255)  in
              FStar_Reflection_Data.Pat_Cons uu____10248
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv,t4) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t4)
           in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
        let brs2 =
          FStar_List.map
            (fun uu___91_10359  ->
               match uu___91_10359 with
               | (pat,uu____10377,t4) ->
                   let uu____10391 = inspect_pat pat  in (uu____10391, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____10398 ->
        ((let uu____10400 =
            let uu____10405 =
              let uu____10406 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____10407 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____10406
                uu____10407
               in
            (FStar_Errors.Warning_CantInspect, uu____10405)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10400);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10420 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10420
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10424 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10424
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10428 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10428
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10435 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10435
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10458 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10458
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10475 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10475
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10494 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10494
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10502 =
          let uu____10505 =
            let uu____10512 =
              let uu____10513 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10513  in
            FStar_Syntax_Syntax.mk uu____10512  in
          uu____10505 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10502
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10523 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10523
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10536 =
          let uu____10539 =
            let uu____10546 =
              let uu____10547 =
                let uu____10560 =
                  let uu____10563 =
                    let uu____10564 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10564]  in
                  FStar_Syntax_Subst.close uu____10563 t2  in
                ((false, [lb]), uu____10560)  in
              FStar_Syntax_Syntax.Tm_let uu____10547  in
            FStar_Syntax_Syntax.mk uu____10546  in
          uu____10539 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10536
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10600 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10600 with
         | (lbs,body) ->
             let uu____10615 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10615)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10653 =
                let uu____10654 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10654  in
              FStar_All.pipe_left wrap uu____10653
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10661 =
                let uu____10662 =
                  let uu____10675 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10691 = pack_pat p1  in
                         (uu____10691, false)) ps
                     in
                  (fv, uu____10675)  in
                FStar_Syntax_Syntax.Pat_cons uu____10662  in
              FStar_All.pipe_left wrap uu____10661
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv,t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1))
           in
        let brs1 =
          FStar_List.map
            (fun uu___92_10737  ->
               match uu___92_10737 with
               | (pat,t1) ->
                   let uu____10754 = pack_pat pat  in
                   (uu____10754, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10802 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10802
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10834 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10834
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10884 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10884
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10927 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10927
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10948 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10948 with
      | (u,ctx_uvars,g_u) ->
          let uu____10980 = FStar_List.hd ctx_uvars  in
          (match uu____10980 with
           | (ctx_uvar,uu____10994) ->
               let g =
                 let uu____10996 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____10996 false
                  in
               (g, g_u))
  
let (proofstate_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11011 = goal_of_goal_ty env typ  in
      match uu____11011 with
      | (g,g_u) ->
          let ps =
            {
              FStar_Tactics_Types.main_context = env;
              FStar_Tactics_Types.main_goal = g;
              FStar_Tactics_Types.all_implicits =
                (g_u.FStar_TypeChecker_Env.implicits);
              FStar_Tactics_Types.goals = [g];
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = (Prims.parse_int "0");
              FStar_Tactics_Types.__dump =
                (fun ps  -> fun msg  -> dump_proofstate ps msg);
              FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc;
              FStar_Tactics_Types.entry_range = FStar_Range.dummyRange;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = (Prims.parse_int "0")
            }  in
          let uu____11027 = FStar_Tactics_Types.goal_witness g  in
          (ps, uu____11027)
  