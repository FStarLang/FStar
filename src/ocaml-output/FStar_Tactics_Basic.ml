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
           let uu____179 = run t1 p  in
           match uu____179 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____186 = t2 a  in run uu____186 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (idtac : unit tac) = ret () 
let (get_uvar_solved :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    let uu____206 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____206 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____224 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____225 =
      let uu____226 = check_goal_solved g  in
      match uu____226 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____230 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____230
       in
    FStar_Util.format2 "%s%s" uu____224 uu____225
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____246 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____246
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____262 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____262
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____283 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____283
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____290) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____300) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____315 =
      let uu____320 =
        let uu____321 = FStar_Tactics_Types.goal_env g  in
        let uu____322 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____321 uu____322  in
      FStar_Syntax_Util.un_squash uu____320  in
    match uu____315 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____328 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____356 =
            let uu____357 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____357  in
          if uu____356 then tacprint msg else ());
         ret ())
  
let dump_goal : 'Auu____365 . 'Auu____365 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  -> let uu____377 = goal_to_string goal  in tacprint uu____377
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____389 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____393 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____393))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____402  ->
    match uu____402 with
    | (msg,ps) ->
        let uu____409 =
          let uu____412 =
            let uu____413 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____413 msg
             in
          let uu____414 =
            let uu____417 =
              let uu____418 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____418  in
            let uu____419 =
              let uu____422 =
                let uu____423 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____424 =
                  let uu____425 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____425  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____423
                  uu____424
                 in
              let uu____428 =
                let uu____431 =
                  let uu____432 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____433 =
                    let uu____434 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____434  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____432
                    uu____433
                   in
                [uu____431]  in
              uu____422 :: uu____428  in
            uu____417 :: uu____419  in
          uu____412 :: uu____414  in
        FStar_String.concat "" uu____409
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____443 =
        let uu____444 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____444  in
      let uu____445 =
        let uu____450 =
          let uu____451 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____451  in
        FStar_Syntax_Print.binders_to_json uu____450  in
      FStar_All.pipe_right uu____443 uu____445  in
    let uu____452 =
      let uu____459 =
        let uu____466 =
          let uu____471 =
            let uu____472 =
              let uu____479 =
                let uu____484 =
                  let uu____485 =
                    let uu____486 = FStar_Tactics_Types.goal_env g  in
                    let uu____487 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____486 uu____487  in
                  FStar_Util.JsonStr uu____485  in
                ("witness", uu____484)  in
              let uu____488 =
                let uu____495 =
                  let uu____500 =
                    let uu____501 =
                      let uu____502 = FStar_Tactics_Types.goal_env g  in
                      let uu____503 = FStar_Tactics_Types.goal_type g  in
                      tts uu____502 uu____503  in
                    FStar_Util.JsonStr uu____501  in
                  ("type", uu____500)  in
                [uu____495]  in
              uu____479 :: uu____488  in
            FStar_Util.JsonAssoc uu____472  in
          ("goal", uu____471)  in
        [uu____466]  in
      ("hyps", g_binders) :: uu____459  in
    FStar_Util.JsonAssoc uu____452
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____536  ->
    match uu____536 with
    | (msg,ps) ->
        let uu____543 =
          let uu____550 =
            let uu____557 =
              let uu____564 =
                let uu____571 =
                  let uu____576 =
                    let uu____577 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____577  in
                  ("goals", uu____576)  in
                let uu____580 =
                  let uu____587 =
                    let uu____592 =
                      let uu____593 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____593  in
                    ("smt-goals", uu____592)  in
                  [uu____587]  in
                uu____571 :: uu____580  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____564
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____557  in
          let uu____616 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____629 =
                let uu____634 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____634)  in
              [uu____629]
            else []  in
          FStar_List.append uu____550 uu____616  in
        FStar_Util.JsonAssoc uu____543
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____664  ->
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
         (let uu____687 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____687 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____705 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____705 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____738 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____738 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____769 =
              let uu____772 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____772  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____769);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____853 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____853
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____861 . Prims.string -> Prims.string -> 'Auu____861 tac =
  fun msg  ->
    fun x  -> let uu____874 = FStar_Util.format1 msg x  in fail uu____874
  
let fail2 :
  'Auu____883 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____883 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____901 = FStar_Util.format2 msg x y  in fail uu____901
  
let fail3 :
  'Auu____912 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____912 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____935 = FStar_Util.format3 msg x y z  in fail uu____935
  
let fail4 :
  'Auu____948 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____948 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____976 = FStar_Util.format4 msg x y z w  in fail uu____976
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1009 = run t ps  in
         match uu____1009 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___93_1033 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___93_1033.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___93_1033.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___93_1033.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___93_1033.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___93_1033.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___93_1033.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___93_1033.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___93_1033.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___93_1033.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___93_1033.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1060 = trytac' t  in
    bind uu____1060
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1087 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1123 = trytac t  in run uu____1123 ps
         with
         | FStar_Errors.Err (uu____1139,msg) ->
             (log ps
                (fun uu____1143  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1148,msg,uu____1150) ->
             (log ps
                (fun uu____1153  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1186 = run t ps  in
           match uu____1186 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1205  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1226 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1226
         then
           let uu____1227 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1228 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1227
             uu____1228
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1240 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1240
            then
              let uu____1241 = FStar_Util.string_of_bool res  in
              let uu____1242 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1243 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1241 uu____1242 uu____1243
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1251,msg) ->
             mlog
               (fun uu____1254  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1256  -> ret false)
         | FStar_Errors.Error (uu____1257,msg,r) ->
             mlog
               (fun uu____1262  ->
                  let uu____1263 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1263) (fun uu____1265  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1288  ->
             (let uu____1290 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1290
              then
                (FStar_Options.push ();
                 (let uu____1292 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1294 =
                let uu____1297 = __do_unify env t1 t2  in
                bind uu____1297
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
              bind uu____1294
                (fun r  ->
                   (let uu____1313 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1313 then FStar_Options.pop () else ());
                   ret r)))
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1329 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1329 with
      | FStar_Pervasives_Native.Some uu____1334 ->
          let uu____1335 =
            let uu____1336 = goal_to_string goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1336  in
          fail uu____1335
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1352 = FStar_Tactics_Types.goal_env goal  in
      let uu____1353 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1352 solution uu____1353
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1359 =
         let uu___98_1360 = p  in
         let uu____1361 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___98_1360.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___98_1360.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___98_1360.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1361;
           FStar_Tactics_Types.smt_goals =
             (uu___98_1360.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___98_1360.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___98_1360.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___98_1360.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___98_1360.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___98_1360.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___98_1360.FStar_Tactics_Types.freshness)
         }  in
       set uu____1359)
  
let (dismiss : unit -> unit tac) =
  fun uu____1370  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1377 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1394 = trysolve goal solution  in
      bind uu____1394
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1402 =
                let uu____1403 =
                  let uu____1404 = FStar_Tactics_Types.goal_env goal  in
                  tts uu____1404 solution  in
                let uu____1405 =
                  let uu____1406 = FStar_Tactics_Types.goal_env goal  in
                  let uu____1407 = FStar_Tactics_Types.goal_witness goal  in
                  tts uu____1406 uu____1407  in
                let uu____1408 =
                  let uu____1409 = FStar_Tactics_Types.goal_env goal  in
                  let uu____1410 = FStar_Tactics_Types.goal_type goal  in
                  tts uu____1409 uu____1410  in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1403
                  uu____1405 uu____1408
                 in
              fail uu____1402))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___99_1417 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___99_1417.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___99_1417.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___99_1417.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___99_1417.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___99_1417.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___99_1417.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___99_1417.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___99_1417.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___99_1417.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___99_1417.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1436 = FStar_Options.defensive ()  in
    if uu____1436
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1441 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1441)
         in
      let b2 =
        b1 &&
          (let uu____1444 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1444)
         in
      let rec aux b3 e =
        let uu____1456 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1456 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1474 =
        (let uu____1477 = aux b2 env  in Prims.op_Negation uu____1477) &&
          (let uu____1479 = FStar_ST.op_Bang nwarn  in
           uu____1479 < (Prims.parse_int "5"))
         in
      (if uu____1474
       then
         ((let uu____1504 =
             let uu____1505 = FStar_Tactics_Types.goal_type g  in
             uu____1505.FStar_Syntax_Syntax.pos  in
           let uu____1508 =
             let uu____1513 =
               let uu____1514 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1514
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1513)  in
           FStar_Errors.log_issue uu____1504 uu____1508);
          (let uu____1515 =
             let uu____1516 = FStar_ST.op_Bang nwarn  in
             uu____1516 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1515))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___100_1584 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___100_1584.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___100_1584.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___100_1584.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___100_1584.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___100_1584.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___100_1584.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___100_1584.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___100_1584.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___100_1584.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___100_1584.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___101_1604 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___101_1604.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___101_1604.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___101_1604.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___101_1604.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___101_1604.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___101_1604.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___101_1604.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___101_1604.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___101_1604.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___101_1604.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___102_1624 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___102_1624.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___102_1624.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___102_1624.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___102_1624.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___102_1624.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___102_1624.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___102_1624.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___102_1624.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___102_1624.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___102_1624.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___103_1644 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___103_1644.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___103_1644.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___103_1644.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___103_1644.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___103_1644.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___103_1644.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___103_1644.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___103_1644.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___103_1644.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___103_1644.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1655  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___104_1669 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___104_1669.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___104_1669.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___104_1669.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___104_1669.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___104_1669.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___104_1669.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___104_1669.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___104_1669.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___104_1669.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___104_1669.FStar_Tactics_Types.freshness)
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
        let uu____1707 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1707 with
        | (u,ctx_uvar,g_u) ->
            let uu____1741 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1741
              (fun uu____1750  ->
                 let uu____1751 =
                   let uu____1756 =
                     let uu____1757 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1757  in
                   (u, uu____1756)  in
                 ret uu____1751)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1775 = FStar_Syntax_Util.un_squash t  in
    match uu____1775 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1785 =
          let uu____1786 = FStar_Syntax_Subst.compress t'  in
          uu____1786.FStar_Syntax_Syntax.n  in
        (match uu____1785 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1790 -> false)
    | uu____1791 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1801 = FStar_Syntax_Util.un_squash t  in
    match uu____1801 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1811 =
          let uu____1812 = FStar_Syntax_Subst.compress t'  in
          uu____1812.FStar_Syntax_Syntax.n  in
        (match uu____1811 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1816 -> false)
    | uu____1817 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1828  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1839 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1839 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1846 = goal_to_string hd1  in
                    let uu____1847 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1846 uu____1847);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1854  ->
    let uu____1857 =
      let uu____1860 = cur_goal ()  in
      bind uu____1860
        (fun g  ->
           (let uu____1867 =
              let uu____1868 = FStar_Tactics_Types.goal_type g  in
              uu____1868.FStar_Syntax_Syntax.pos  in
            let uu____1871 =
              let uu____1876 =
                let uu____1877 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1877
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1876)  in
            FStar_Errors.log_issue uu____1867 uu____1871);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1857
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1888  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___105_1898 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___105_1898.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___105_1898.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___105_1898.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___105_1898.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___105_1898.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___105_1898.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___105_1898.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___105_1898.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___105_1898.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___105_1898.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1899 = set ps1  in
         bind uu____1899
           (fun uu____1904  ->
              let uu____1905 = FStar_BigInt.of_int_fs n1  in ret uu____1905))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1912  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1920 = FStar_BigInt.of_int_fs n1  in ret uu____1920)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1933  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1941 = FStar_BigInt.of_int_fs n1  in ret uu____1941)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1954  ->
    let uu____1957 = cur_goal ()  in
    bind uu____1957 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1989 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1989 phi  in
          let uu____1990 = new_uvar reason env typ  in
          bind uu____1990
            (fun uu____2005  ->
               match uu____2005 with
               | (uu____2012,ctx_uvar) ->
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
             (fun uu____2057  ->
                let uu____2058 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2058)
             (fun uu____2060  ->
                try
                  let uu____2080 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____2080
                with
                | FStar_Errors.Err (uu____2107,msg) ->
                    let uu____2109 = tts e t  in
                    let uu____2110 =
                      let uu____2111 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2111
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2109 uu____2110 msg
                | FStar_Errors.Error (uu____2118,msg,uu____2120) ->
                    let uu____2121 = tts e t  in
                    let uu____2122 =
                      let uu____2123 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2123
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2121 uu____2122 msg))
  
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
  fun uu____2150  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___108_2168 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___108_2168.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___108_2168.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___108_2168.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___108_2168.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___108_2168.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___108_2168.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___108_2168.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___108_2168.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___108_2168.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___108_2168.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2192 = get_guard_policy ()  in
      bind uu____2192
        (fun old_pol  ->
           let uu____2198 = set_guard_policy pol  in
           bind uu____2198
             (fun uu____2202  ->
                bind t
                  (fun r  ->
                     let uu____2206 = set_guard_policy old_pol  in
                     bind uu____2206 (fun uu____2210  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2235 =
            let uu____2236 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2236.FStar_TypeChecker_Env.guard_f  in
          match uu____2235 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2240 = istrivial e f  in
              if uu____2240
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2248 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2248
                           (fun goal  ->
                              let goal1 =
                                let uu___109_2255 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___109_2255.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___109_2255.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_2255.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2256 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2256
                           (fun goal  ->
                              let goal1 =
                                let uu___110_2263 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___110_2263.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___110_2263.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___110_2263.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2271 =
                              let uu____2272 =
                                let uu____2273 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2273
                                 in
                              Prims.op_Negation uu____2272  in
                            if uu____2271
                            then
                              mlog
                                (fun uu____2278  ->
                                   let uu____2279 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2279)
                                (fun uu____2281  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2288 ->
                              mlog
                                (fun uu____2291  ->
                                   let uu____2292 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2292)
                                (fun uu____2294  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2304 =
      let uu____2307 = cur_goal ()  in
      bind uu____2307
        (fun goal  ->
           let uu____2313 =
             let uu____2322 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2322 t  in
           bind uu____2313
             (fun uu____2334  ->
                match uu____2334 with
                | (t1,typ,guard) ->
                    let uu____2346 =
                      let uu____2349 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2349 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2346 (fun uu____2351  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2304
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2380 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2380 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2391  ->
    let uu____2394 = cur_goal ()  in
    bind uu____2394
      (fun goal  ->
         let uu____2400 =
           let uu____2401 = FStar_Tactics_Types.goal_env goal  in
           let uu____2402 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2401 uu____2402  in
         if uu____2400
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2406 =
              let uu____2407 = FStar_Tactics_Types.goal_env goal  in
              let uu____2408 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2407 uu____2408  in
            fail1 "Not a trivial goal: %s" uu____2406))
  
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
          FStar_List.iter
            (fun imp  ->
               match imp with
               | (s,tm,uv,rng,b) ->
                   let uu____2472 = get_uvar_solved uv  in
                   (match uu____2472 with
                    | FStar_Pervasives_Native.None  ->
                        ((let uu____2476 =
                            FStar_TypeChecker_Rel.guard_to_string e g  in
                          let uu____2477 =
                            FStar_Syntax_Print.ctx_uvar_to_string uv  in
                          FStar_Util.print3
                            "GG, implicit from guard\n>>%s\n\n(%s, %s)\n"
                            uu____2476 s uu____2477);
                         failwith "")
                    | FStar_Pervasives_Native.Some uu____2478 -> ()))
            g.FStar_TypeChecker_Env.implicits;
          (let uu____2479 =
             let uu____2480 = FStar_TypeChecker_Rel.simplify_guard e g  in
             uu____2480.FStar_TypeChecker_Env.guard_f  in
           match uu____2479 with
           | FStar_TypeChecker_Common.Trivial  ->
               ret FStar_Pervasives_Native.None
           | FStar_TypeChecker_Common.NonTrivial f ->
               let uu____2488 = istrivial e f  in
               if uu____2488
               then ret FStar_Pervasives_Native.None
               else
                 (let uu____2496 = mk_irrelevant_goal reason e f opts  in
                  bind uu____2496
                    (fun goal  ->
                       ret
                         (FStar_Pervasives_Native.Some
                            (let uu___113_2506 = goal  in
                             {
                               FStar_Tactics_Types.goal_main_env =
                                 (uu___113_2506.FStar_Tactics_Types.goal_main_env);
                               FStar_Tactics_Types.goal_ctx_uvar =
                                 (uu___113_2506.FStar_Tactics_Types.goal_ctx_uvar);
                               FStar_Tactics_Types.opts =
                                 (uu___113_2506.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = true
                             })))))
  
let (smt : unit -> unit tac) =
  fun uu____2513  ->
    let uu____2516 = cur_goal ()  in
    bind uu____2516
      (fun g  ->
         let uu____2522 = is_irrelevant g  in
         if uu____2522
         then bind __dismiss (fun uu____2526  -> add_smt_goals [g])
         else
           (let uu____2528 =
              let uu____2529 = FStar_Tactics_Types.goal_env g  in
              let uu____2530 = FStar_Tactics_Types.goal_type g  in
              tts uu____2529 uu____2530  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2528))
  
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
             let uu____2579 =
               try
                 let uu____2613 =
                   let uu____2622 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2622 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2613
               with | uu____2644 -> fail "divide: not enough goals"  in
             bind uu____2579
               (fun uu____2671  ->
                  match uu____2671 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___114_2697 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___114_2697.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___114_2697.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___114_2697.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___114_2697.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___114_2697.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___114_2697.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___114_2697.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___114_2697.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___114_2697.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___115_2699 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___115_2699.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___115_2699.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___115_2699.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___115_2699.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___115_2699.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___115_2699.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___115_2699.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___115_2699.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___115_2699.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2700 = set lp  in
                      bind uu____2700
                        (fun uu____2708  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2722 = set rp  in
                                     bind uu____2722
                                       (fun uu____2730  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___116_2746 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___116_2746.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___116_2746.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___116_2746.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___116_2746.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___116_2746.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___116_2746.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___116_2746.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___116_2746.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___116_2746.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2747 = set p'
                                                       in
                                                    bind uu____2747
                                                      (fun uu____2755  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2776 = divide FStar_BigInt.one f idtac  in
    bind uu____2776
      (fun uu____2789  -> match uu____2789 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2826::uu____2827 ->
             let uu____2830 =
               let uu____2839 = map tau  in
               divide FStar_BigInt.one tau uu____2839  in
             bind uu____2830
               (fun uu____2857  ->
                  match uu____2857 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2898 =
        bind t1
          (fun uu____2903  ->
             let uu____2904 = map t2  in
             bind uu____2904 (fun uu____2912  -> ret ()))
         in
      focus uu____2898
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2921  ->
    let uu____2924 =
      let uu____2927 = cur_goal ()  in
      bind uu____2927
        (fun goal  ->
           let uu____2936 =
             let uu____2943 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2943  in
           match uu____2936 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2952 =
                 let uu____2953 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2953  in
               if uu____2952
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2958 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2958 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2968 = new_uvar "intro" env' typ'  in
                  bind uu____2968
                    (fun uu____2984  ->
                       match uu____2984 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3004 = set_solution goal sol  in
                           bind uu____3004
                             (fun uu____3010  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3012 = replace_cur g  in
                                bind uu____3012 (fun uu____3016  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3021 =
                 let uu____3022 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3023 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3022 uu____3023  in
               fail1 "goal is not an arrow (%s)" uu____3021)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2924
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3038  ->
    let uu____3045 = cur_goal ()  in
    bind uu____3045
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3062 =
            let uu____3069 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3069  in
          match uu____3062 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3082 =
                let uu____3083 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3083  in
              if uu____3082
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3096 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3096
                    in
                 let bs =
                   let uu____3104 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3104; b]  in
                 let env' =
                   let uu____3122 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3122 bs  in
                 let uu____3123 =
                   let uu____3130 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3130  in
                 bind uu____3123
                   (fun uu____3149  ->
                      match uu____3149 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3163 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3166 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3163
                              FStar_Parser_Const.effect_Tot_lid uu____3166 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3180 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3180 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3202 =
                                   let uu____3203 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3203.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3202
                                  in
                               let uu____3216 = set_solution goal tm  in
                               bind uu____3216
                                 (fun uu____3225  ->
                                    let uu____3226 =
                                      replace_cur
                                        (let uu___119_3231 = goal  in
                                         {
                                           FStar_Tactics_Types.goal_main_env
                                             =
                                             (uu___119_3231.FStar_Tactics_Types.goal_main_env);
                                           FStar_Tactics_Types.goal_ctx_uvar
                                             = ctx_uvar_u;
                                           FStar_Tactics_Types.opts =
                                             (uu___119_3231.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___119_3231.FStar_Tactics_Types.is_guard)
                                         })
                                       in
                                    bind uu____3226
                                      (fun uu____3238  ->
                                         let uu____3239 =
                                           let uu____3244 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3244, b)  in
                                         ret uu____3239)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3253 =
                let uu____3254 = FStar_Tactics_Types.goal_env goal  in
                let uu____3255 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3254 uu____3255  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3253))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3273 = cur_goal ()  in
    bind uu____3273
      (fun goal  ->
         mlog
           (fun uu____3280  ->
              let uu____3281 =
                let uu____3282 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3282  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3281)
           (fun uu____3287  ->
              let steps =
                let uu____3291 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3291
                 in
              let t =
                let uu____3295 = FStar_Tactics_Types.goal_env goal  in
                let uu____3296 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3295 uu____3296  in
              let uu____3297 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3297))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3321 =
          mlog
            (fun uu____3326  ->
               let uu____3327 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3327)
            (fun uu____3329  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3335 -> g.FStar_Tactics_Types.opts
                      | uu____3338 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3343  ->
                         let uu____3344 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3344)
                      (fun uu____3347  ->
                         let uu____3348 = __tc e t  in
                         bind uu____3348
                           (fun uu____3369  ->
                              match uu____3369 with
                              | (t1,uu____3379,uu____3380) ->
                                  let steps =
                                    let uu____3384 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3384
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3321
  
let (refine_intro : unit -> unit tac) =
  fun uu____3398  ->
    let uu____3401 =
      let uu____3404 = cur_goal ()  in
      bind uu____3404
        (fun g  ->
           let uu____3411 =
             let uu____3422 = FStar_Tactics_Types.goal_env g  in
             let uu____3423 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3422 uu____3423
              in
           match uu____3411 with
           | (uu____3426,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3451 =
                 let uu____3456 =
                   let uu____3461 =
                     let uu____3462 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3462]  in
                   FStar_Syntax_Subst.open_term uu____3461 phi  in
                 match uu____3456 with
                 | (bvs,phi1) ->
                     let uu____3481 =
                       let uu____3482 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3482  in
                     (uu____3481, phi1)
                  in
               (match uu____3451 with
                | (bv1,phi1) ->
                    let uu____3495 =
                      let uu____3498 = FStar_Tactics_Types.goal_env g  in
                      let uu____3499 =
                        let uu____3500 =
                          let uu____3503 =
                            let uu____3504 =
                              let uu____3511 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3511)  in
                            FStar_Syntax_Syntax.NT uu____3504  in
                          [uu____3503]  in
                        FStar_Syntax_Subst.subst uu____3500 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3498
                        uu____3499 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3495
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3519  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3401
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3538 = cur_goal ()  in
      bind uu____3538
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3546 = FStar_Tactics_Types.goal_env goal  in
               let uu____3547 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3546 uu____3547
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3549 = __tc env t  in
           bind uu____3549
             (fun uu____3568  ->
                match uu____3568 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3583  ->
                         let uu____3584 =
                           let uu____3585 = FStar_Tactics_Types.goal_env goal
                              in
                           tts uu____3585 typ  in
                         let uu____3586 =
                           let uu____3587 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3587
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3584 uu____3586)
                      (fun uu____3590  ->
                         let uu____3591 =
                           let uu____3594 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3594 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3591
                           (fun uu____3596  ->
                              mlog
                                (fun uu____3600  ->
                                   let uu____3601 =
                                     let uu____3602 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     tts uu____3602 typ  in
                                   let uu____3603 =
                                     let uu____3604 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3605 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     tts uu____3604 uu____3605  in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3601 uu____3603)
                                (fun uu____3608  ->
                                   let uu____3609 =
                                     let uu____3612 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3613 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3612 typ uu____3613  in
                                   bind uu____3609
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3619 =
                                             let uu____3620 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3620 t1  in
                                           let uu____3621 =
                                             let uu____3622 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3622 typ  in
                                           let uu____3623 =
                                             let uu____3624 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3625 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3624 uu____3625  in
                                           let uu____3626 =
                                             let uu____3627 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3628 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3627 uu____3628  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3619 uu____3621 uu____3623
                                             uu____3626)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3643 =
        mlog
          (fun uu____3648  ->
             let uu____3649 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3649)
          (fun uu____3652  ->
             let uu____3653 =
               let uu____3660 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3660  in
             bind uu____3653
               (fun uu___88_3669  ->
                  match uu___88_3669 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3678 =
                        let uu____3685 =
                          let uu____3688 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3688
                            (fun uu____3693  ->
                               let uu____3694 = refine_intro ()  in
                               bind uu____3694
                                 (fun uu____3698  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3685  in
                      bind uu____3678
                        (fun uu___87_3705  ->
                           match uu___87_3705 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3713 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3643
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3742 =
             let uu____3745 =
               let uu____3748 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3748  in
             FStar_Util.set_elements uu____3745  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3742
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
          let uu____3826 = f x  in
          bind uu____3826
            (fun y  ->
               let uu____3834 = mapM f xs  in
               bind uu____3834 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3854 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3874 = cur_goal ()  in
        bind uu____3874
          (fun goal  ->
             mlog
               (fun uu____3881  ->
                  let uu____3882 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3882)
               (fun uu____3885  ->
                  let uu____3886 =
                    let uu____3891 =
                      let uu____3894 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3894  in
                    trytac_exn uu____3891  in
                  bind uu____3886
                    (fun uu___89_3901  ->
                       match uu___89_3901 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3909  ->
                                let uu____3910 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3910)
                             (fun uu____3913  ->
                                let uu____3914 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3914 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3938  ->
                                         let uu____3939 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3939)
                                      (fun uu____3942  ->
                                         let uu____3943 =
                                           let uu____3944 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3944  in
                                         if uu____3943
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3948 =
                                              let uu____3955 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3955
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3948
                                              (fun uu____3966  ->
                                                 match uu____3966 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____3993 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____3993
                                                        in
                                                     let uu____3996 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____3996
                                                       (fun uu____4004  ->
                                                          let u1 =
                                                            let uu____4006 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____4006
                                                              u
                                                             in
                                                          let uu____4007 =
                                                            let uu____4008 =
                                                              let uu____4011
                                                                =
                                                                let uu____4012
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4012
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4011
                                                               in
                                                            uu____4008.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4007
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4040)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4064
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4064
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    add_goals
                                                                    [(
                                                                    let uu___120_4069
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___120_4069.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___120_4069.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })])
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4124 =
        mlog
          (fun uu____4129  ->
             let uu____4130 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4130)
          (fun uu____4133  ->
             let uu____4134 = cur_goal ()  in
             bind uu____4134
               (fun goal  ->
                  let uu____4140 =
                    let uu____4149 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4149 tm  in
                  bind uu____4140
                    (fun uu____4163  ->
                       match uu____4163 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4176 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4176 typ  in
                           let uu____4177 =
                             let uu____4180 =
                               let uu____4183 = __apply uopt tm1 typ1  in
                               bind uu____4183
                                 (fun uu____4188  ->
                                    let uu____4189 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4189 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4180  in
                           let uu____4190 =
                             let uu____4193 =
                               let uu____4194 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4194 tm1  in
                             let uu____4195 =
                               let uu____4196 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4196 typ1  in
                             let uu____4197 =
                               let uu____4198 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4199 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4198 uu____4199  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4193 uu____4195 uu____4197
                              in
                           try_unif uu____4177 uu____4190)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4124
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4222 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4222
    then
      let uu____4229 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4248 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4289 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4229 with
      | (pre,post) ->
          let post1 =
            let uu____4325 =
              let uu____4334 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4334]  in
            FStar_Syntax_Util.mk_app post uu____4325  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4358 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4358
       then
         let uu____4365 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4365
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4398 =
      let uu____4401 =
        mlog
          (fun uu____4406  ->
             let uu____4407 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4407)
          (fun uu____4411  ->
             let is_unit_t t =
               let uu____4418 =
                 let uu____4419 = FStar_Syntax_Subst.compress t  in
                 uu____4419.FStar_Syntax_Syntax.n  in
               match uu____4418 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4423 -> false  in
             let uu____4424 = cur_goal ()  in
             bind uu____4424
               (fun goal  ->
                  let uu____4430 =
                    let uu____4439 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4439 tm  in
                  bind uu____4430
                    (fun uu____4454  ->
                       match uu____4454 with
                       | (tm1,t,guard) ->
                           let uu____4466 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4466 with
                            | (bs,comp) ->
                                let uu____4493 = lemma_or_sq comp  in
                                (match uu____4493 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4512 =
                                       FStar_List.fold_left
                                         (fun uu____4554  ->
                                            fun uu____4555  ->
                                              match (uu____4554, uu____4555)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4646 =
                                                    is_unit_t b_t  in
                                                  if uu____4646
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4682 =
                                                       let uu____4695 =
                                                         let uu____4696 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4696.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4699 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4695
                                                         uu____4699 b_t
                                                        in
                                                     match uu____4682 with
                                                     | (u,uu____4715,g_u) ->
                                                         let uu____4729 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4729,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4512 with
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
                                          let uu____4790 =
                                            let uu____4793 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4794 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4795 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4793 uu____4794
                                              uu____4795
                                             in
                                          bind uu____4790
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4803 =
                                                   let uu____4804 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4804 tm1  in
                                                 let uu____4805 =
                                                   let uu____4806 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4807 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4806 uu____4807
                                                    in
                                                 let uu____4808 =
                                                   let uu____4809 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4810 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4809 uu____4810
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4803 uu____4805
                                                   uu____4808
                                               else
                                                 (let uu____4812 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4812
                                                    (fun uu____4817  ->
                                                       let uu____4818 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4818
                                                         (fun uu____4826  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4851
                                                                  =
                                                                  let uu____4854
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4854
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4851
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
                                                                   let uu____4889
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4889)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4905
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4905
                                                              with
                                                              | (hd1,uu____4921)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4943)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4964
                                                                    -> false)
                                                               in
                                                            let uu____4965 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5035
                                                                     ->
                                                                    match uu____5035
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range,uu____5060)
                                                                    ->
                                                                    let uu____5061
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5061
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5087)
                                                                    ->
                                                                    let uu____5108
                                                                    =
                                                                    let uu____5109
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5109.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5108
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5123)
                                                                    ->
                                                                    let env =
                                                                    let uu___123_5145
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___123_5145.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let goal_ty
                                                                    =
                                                                    bnorm env
                                                                    ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let goal1
                                                                    =
                                                                    FStar_Tactics_Types.goal_with_type
                                                                    (let uu___124_5150
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___124_5150.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___124_5150.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___124_5150.FStar_Tactics_Types.is_guard)
                                                                    })
                                                                    goal_ty
                                                                     in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5163
                                                                    ->
                                                                    let env =
                                                                    let uu___125_5165
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___125_5165.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5167
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5167
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
                                                                    let uu____5170
                                                                    =
                                                                    let uu____5177
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5177
                                                                    term1  in
                                                                    match uu____5170
                                                                    with
                                                                    | 
                                                                    (uu____5178,uu____5179,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5181
                                                                    =
                                                                    let uu____5186
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5186
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5181
                                                                    (fun
                                                                    uu___90_5198
                                                                     ->
                                                                    match uu___90_5198
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
                                                            bind uu____4965
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5266
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5266
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5288
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5288
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5349
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5349
                                                                    then
                                                                    let uu____5352
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5352
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
                                                                    let uu____5366
                                                                    =
                                                                    let uu____5367
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5367
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5366)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5368
                                                                   =
                                                                   let uu____5371
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5371
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5368
                                                                   (fun
                                                                    uu____5374
                                                                     ->
                                                                    let uu____5375
                                                                    =
                                                                    let uu____5378
                                                                    =
                                                                    let uu____5379
                                                                    =
                                                                    let uu____5380
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5381
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5380
                                                                    uu____5381
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5379
                                                                     in
                                                                    if
                                                                    uu____5378
                                                                    then
                                                                    let uu____5384
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5384
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5375
                                                                    (fun
                                                                    uu____5388
                                                                     ->
                                                                    let uu____5389
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5389
                                                                    (fun
                                                                    uu____5393
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4401  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4398
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5415 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5415 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5425::(e1,uu____5427)::(e2,uu____5429)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5472 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5496 = destruct_eq' typ  in
    match uu____5496 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5526 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5526 with
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
        let uu____5588 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5588 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5636 = aux e'  in
               FStar_Util.map_opt uu____5636
                 (fun uu____5660  ->
                    match uu____5660 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5681 = aux e  in
      FStar_Util.map_opt uu____5681
        (fun uu____5705  ->
           match uu____5705 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5772 =
            let uu____5781 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5781  in
          FStar_Util.map_opt uu____5772
            (fun uu____5796  ->
               match uu____5796 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___126_5815 = bv  in
                     let uu____5816 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___126_5815.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___126_5815.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5816
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___127_5824 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5825 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5832 =
                       let uu____5835 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5835  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___127_5824.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5825;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5832;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___127_5824.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___127_5824.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___127_5824.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___128_5836 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___128_5836.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___128_5836.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___128_5836.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5846 = cur_goal ()  in
    bind uu____5846
      (fun goal  ->
         let uu____5854 = h  in
         match uu____5854 with
         | (bv,uu____5858) ->
             mlog
               (fun uu____5862  ->
                  let uu____5863 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5864 =
                    let uu____5865 = FStar_Tactics_Types.goal_env goal  in
                    tts uu____5865 bv.FStar_Syntax_Syntax.sort  in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5863
                    uu____5864)
               (fun uu____5868  ->
                  let uu____5869 =
                    let uu____5878 = FStar_Tactics_Types.goal_env goal  in
                    split_env bv uu____5878  in
                  match uu____5869 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5899 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5899 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5914 =
                             let uu____5915 = FStar_Syntax_Subst.compress x
                                in
                             uu____5915.FStar_Syntax_Syntax.n  in
                           (match uu____5914 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___129_5932 = bv1  in
                                  let uu____5933 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___129_5932.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___129_5932.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5933
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let new_env = push_bvs e0 (bv :: bvs1)  in
                                let new_goal =
                                  let uu___130_5941 =
                                    goal.FStar_Tactics_Types.goal_ctx_uvar
                                     in
                                  let uu____5942 =
                                    FStar_TypeChecker_Env.all_binders new_env
                                     in
                                  let uu____5949 =
                                    let uu____5952 =
                                      FStar_Tactics_Types.goal_type goal  in
                                    FStar_Syntax_Subst.subst s uu____5952  in
                                  {
                                    FStar_Syntax_Syntax.ctx_uvar_head =
                                      (uu___130_5941.FStar_Syntax_Syntax.ctx_uvar_head);
                                    FStar_Syntax_Syntax.ctx_uvar_gamma =
                                      (new_env.FStar_TypeChecker_Env.gamma);
                                    FStar_Syntax_Syntax.ctx_uvar_binders =
                                      uu____5942;
                                    FStar_Syntax_Syntax.ctx_uvar_typ =
                                      uu____5949;
                                    FStar_Syntax_Syntax.ctx_uvar_reason =
                                      (uu___130_5941.FStar_Syntax_Syntax.ctx_uvar_reason);
                                    FStar_Syntax_Syntax.ctx_uvar_should_check
                                      =
                                      (uu___130_5941.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                    FStar_Syntax_Syntax.ctx_uvar_range =
                                      (uu___130_5941.FStar_Syntax_Syntax.ctx_uvar_range)
                                  }  in
                                replace_cur
                                  (let uu___131_5955 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___131_5955.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       new_goal;
                                     FStar_Tactics_Types.opts =
                                       (uu___131_5955.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___131_5955.FStar_Tactics_Types.is_guard)
                                   })
                            | uu____5956 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5957 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5978 = cur_goal ()  in
      bind uu____5978
        (fun goal  ->
           let uu____5989 = b  in
           match uu____5989 with
           | (bv,uu____5993) ->
               let bv' =
                 let uu____5995 =
                   let uu___132_5996 = bv  in
                   let uu____5997 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5997;
                     FStar_Syntax_Syntax.index =
                       (uu___132_5996.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___132_5996.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5995  in
               let s1 =
                 let uu____6001 =
                   let uu____6002 =
                     let uu____6009 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____6009)  in
                   FStar_Syntax_Syntax.NT uu____6002  in
                 [uu____6001]  in
               let uu____6014 = subst_goal bv bv' s1 goal  in
               (match uu____6014 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6029 = cur_goal ()  in
    bind uu____6029
      (fun goal  ->
         let uu____6038 = b  in
         match uu____6038 with
         | (bv,uu____6042) ->
             let uu____6043 =
               let uu____6052 = FStar_Tactics_Types.goal_env goal  in
               split_env bv uu____6052  in
             (match uu____6043 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____6073 = FStar_Syntax_Util.type_u ()  in
                  (match uu____6073 with
                   | (ty,u) ->
                       let uu____6082 = new_uvar "binder_retype" e0 ty  in
                       bind uu____6082
                         (fun uu____6100  ->
                            match uu____6100 with
                            | (t',u_t') ->
                                let bv'' =
                                  let uu___133_6110 = bv  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___133_6110.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___133_6110.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t'
                                  }  in
                                let s =
                                  let uu____6114 =
                                    let uu____6115 =
                                      let uu____6122 =
                                        FStar_Syntax_Syntax.bv_to_name bv''
                                         in
                                      (bv, uu____6122)  in
                                    FStar_Syntax_Syntax.NT uu____6115  in
                                  [uu____6114]  in
                                let bvs1 =
                                  FStar_List.map
                                    (fun b1  ->
                                       let uu___134_6134 = b1  in
                                       let uu____6135 =
                                         FStar_Syntax_Subst.subst s
                                           b1.FStar_Syntax_Syntax.sort
                                          in
                                       {
                                         FStar_Syntax_Syntax.ppname =
                                           (uu___134_6134.FStar_Syntax_Syntax.ppname);
                                         FStar_Syntax_Syntax.index =
                                           (uu___134_6134.FStar_Syntax_Syntax.index);
                                         FStar_Syntax_Syntax.sort =
                                           uu____6135
                                       }) bvs
                                   in
                                let env' = push_bvs e0 (bv'' :: bvs1)  in
                                bind __dismiss
                                  (fun uu____6142  ->
                                     let new_goal =
                                       let uu____6144 =
                                         FStar_Tactics_Types.goal_with_env
                                           goal env'
                                          in
                                       let uu____6145 =
                                         let uu____6146 =
                                           FStar_Tactics_Types.goal_type goal
                                            in
                                         FStar_Syntax_Subst.subst s
                                           uu____6146
                                          in
                                       FStar_Tactics_Types.goal_with_type
                                         uu____6144 uu____6145
                                        in
                                     let uu____6147 = add_goals [new_goal]
                                        in
                                     bind uu____6147
                                       (fun uu____6152  ->
                                          let uu____6153 =
                                            FStar_Syntax_Util.mk_eq2
                                              (FStar_Syntax_Syntax.U_succ u)
                                              ty bv.FStar_Syntax_Syntax.sort
                                              t'
                                             in
                                          add_irrelevant_goal
                                            "binder_retype equation" e0
                                            uu____6153
                                            goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6172 = cur_goal ()  in
      bind uu____6172
        (fun goal  ->
           let uu____6181 = b  in
           match uu____6181 with
           | (bv,uu____6185) ->
               let uu____6186 =
                 let uu____6195 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6195  in
               (match uu____6186 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____6219 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____6219
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___135_6224 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___135_6224.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___135_6224.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    let uu____6226 =
                      FStar_Tactics_Types.goal_with_env goal env'  in
                    replace_cur uu____6226))
  
let (revert : unit -> unit tac) =
  fun uu____6233  ->
    let uu____6236 = cur_goal ()  in
    bind uu____6236
      (fun goal  ->
         let uu____6242 =
           let uu____6249 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6249  in
         match uu____6242 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6265 =
                 let uu____6268 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6268  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6265
                in
             let uu____6277 = new_uvar "revert" env' typ'  in
             bind uu____6277
               (fun uu____6292  ->
                  match uu____6292 with
                  | (r,u_r) ->
                      let uu____6301 =
                        let uu____6304 =
                          let uu____6305 =
                            let uu____6306 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6306.FStar_Syntax_Syntax.pos  in
                          let uu____6309 =
                            let uu____6314 =
                              let uu____6315 =
                                let uu____6322 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6322  in
                              [uu____6315]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6314  in
                          uu____6309 FStar_Pervasives_Native.None uu____6305
                           in
                        set_solution goal uu____6304  in
                      bind uu____6301
                        (fun uu____6339  ->
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
      let uu____6351 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6351
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6364 = cur_goal ()  in
    bind uu____6364
      (fun goal  ->
         mlog
           (fun uu____6372  ->
              let uu____6373 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6374 =
                let uu____6375 =
                  let uu____6376 =
                    let uu____6383 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6383  in
                  FStar_All.pipe_right uu____6376 FStar_List.length  in
                FStar_All.pipe_right uu____6375 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6373 uu____6374)
           (fun uu____6396  ->
              let uu____6397 =
                let uu____6406 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6406  in
              match uu____6397 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6445 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6445
                        then
                          let uu____6448 =
                            let uu____6449 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6449
                             in
                          fail uu____6448
                        else check1 bvs2
                     in
                  let uu____6451 =
                    let uu____6452 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6452  in
                  if uu____6451
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6456 = check1 bvs  in
                     bind uu____6456
                       (fun uu____6462  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6464 =
                            let uu____6471 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6471  in
                          bind uu____6464
                            (fun uu____6480  ->
                               match uu____6480 with
                               | (ut,uvar_ut) ->
                                   let uu____6489 = set_solution goal ut  in
                                   bind uu____6489
                                     (fun uu____6494  ->
                                        let uu____6495 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6495))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6502  ->
    let uu____6505 = cur_goal ()  in
    bind uu____6505
      (fun goal  ->
         let uu____6511 =
           let uu____6518 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6518  in
         match uu____6511 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6526) ->
             let uu____6531 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6531)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6541 = cur_goal ()  in
    bind uu____6541
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6551 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6551  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6554  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6564 = cur_goal ()  in
    bind uu____6564
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6574 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6574  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6577  -> add_goals [g']))
  
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
            let uu____6617 = FStar_Syntax_Subst.compress t  in
            uu____6617.FStar_Syntax_Syntax.n  in
          let uu____6620 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___139_6626 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___139_6626.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___139_6626.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6620
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6642 =
                   let uu____6643 = FStar_Syntax_Subst.compress t1  in
                   uu____6643.FStar_Syntax_Syntax.n  in
                 match uu____6642 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6670 = ff hd1  in
                     bind uu____6670
                       (fun hd2  ->
                          let fa uu____6692 =
                            match uu____6692 with
                            | (a,q) ->
                                let uu____6705 = ff a  in
                                bind uu____6705 (fun a1  -> ret (a1, q))
                             in
                          let uu____6718 = mapM fa args  in
                          bind uu____6718
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6784 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6784 with
                      | (bs1,t') ->
                          let uu____6793 =
                            let uu____6796 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6796 t'  in
                          bind uu____6793
                            (fun t''  ->
                               let uu____6800 =
                                 let uu____6801 =
                                   let uu____6818 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6825 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6818, uu____6825, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6801  in
                               ret uu____6800))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6894 = ff hd1  in
                     bind uu____6894
                       (fun hd2  ->
                          let ffb br =
                            let uu____6909 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6909 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6941 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6941  in
                                let uu____6942 = ff1 e  in
                                bind uu____6942
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6957 = mapM ffb brs  in
                          bind uu____6957
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7001;
                          FStar_Syntax_Syntax.lbtyp = uu____7002;
                          FStar_Syntax_Syntax.lbeff = uu____7003;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7005;
                          FStar_Syntax_Syntax.lbpos = uu____7006;_}::[]),e)
                     ->
                     let lb =
                       let uu____7031 =
                         let uu____7032 = FStar_Syntax_Subst.compress t1  in
                         uu____7032.FStar_Syntax_Syntax.n  in
                       match uu____7031 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7036) -> lb
                       | uu____7049 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7058 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7058
                         (fun def1  ->
                            ret
                              (let uu___136_7064 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___136_7064.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___136_7064.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___136_7064.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___136_7064.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___136_7064.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___136_7064.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7065 = fflb lb  in
                     bind uu____7065
                       (fun lb1  ->
                          let uu____7075 =
                            let uu____7080 =
                              let uu____7081 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7081]  in
                            FStar_Syntax_Subst.open_term uu____7080 e  in
                          match uu____7075 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7105 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7105  in
                              let uu____7106 = ff1 e1  in
                              bind uu____7106
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7147 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7147
                         (fun def  ->
                            ret
                              (let uu___137_7153 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___137_7153.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___137_7153.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___137_7153.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___137_7153.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___137_7153.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___137_7153.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7154 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7154 with
                      | (lbs1,e1) ->
                          let uu____7169 = mapM fflb lbs1  in
                          bind uu____7169
                            (fun lbs2  ->
                               let uu____7181 = ff e1  in
                               bind uu____7181
                                 (fun e2  ->
                                    let uu____7189 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7189 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7257 = ff t2  in
                     bind uu____7257
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7288 = ff t2  in
                     bind uu____7288
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7295 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___138_7302 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___138_7302.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___138_7302.FStar_Syntax_Syntax.vars)
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
            let uu____7339 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7339 with
            | (t1,lcomp,g) ->
                let uu____7351 =
                  (let uu____7354 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7354) ||
                    (let uu____7356 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7356)
                   in
                if uu____7351
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7366 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7366
                       (fun uu____7382  ->
                          match uu____7382 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7395  ->
                                    let uu____7396 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7397 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7396 uu____7397);
                               (let uu____7398 =
                                  let uu____7401 =
                                    let uu____7402 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7402 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7401
                                    opts
                                   in
                                bind uu____7398
                                  (fun uu____7405  ->
                                     let uu____7406 =
                                       bind tau
                                         (fun uu____7412  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7418  ->
                                                 let uu____7419 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7420 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7419 uu____7420);
                                            ret ut1)
                                        in
                                     focus uu____7406))))
                      in
                   let uu____7421 = trytac' rewrite_eq  in
                   bind uu____7421
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
          let uu____7619 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7619
            (fun t1  ->
               let uu____7627 =
                 f env
                   (let uu___142_7636 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___142_7636.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___142_7636.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7627
                 (fun uu____7652  ->
                    match uu____7652 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7675 =
                               let uu____7676 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7676.FStar_Syntax_Syntax.n  in
                             match uu____7675 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7709 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7709
                                   (fun uu____7734  ->
                                      match uu____7734 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7750 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7750
                                            (fun uu____7777  ->
                                               match uu____7777 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___140_7807 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___140_7807.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___140_7807.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7843 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7843 with
                                  | (bs1,t') ->
                                      let uu____7858 =
                                        let uu____7865 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7865 ctrl1 t'
                                         in
                                      bind uu____7858
                                        (fun uu____7883  ->
                                           match uu____7883 with
                                           | (t'',ctrl2) ->
                                               let uu____7898 =
                                                 let uu____7905 =
                                                   let uu___141_7908 = t4  in
                                                   let uu____7911 =
                                                     let uu____7912 =
                                                       let uu____7929 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7936 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7929,
                                                         uu____7936, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7912
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7911;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___141_7908.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___141_7908.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7905, ctrl2)  in
                                               ret uu____7898))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7983 -> ret (t3, ctrl1))))

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
              let uu____8026 = ctrl_tac_fold f env ctrl t  in
              bind uu____8026
                (fun uu____8050  ->
                   match uu____8050 with
                   | (t1,ctrl1) ->
                       let uu____8065 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8065
                         (fun uu____8092  ->
                            match uu____8092 with
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
              let uu____8174 =
                let uu____8181 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8181
                  (fun uu____8190  ->
                     let uu____8191 = ctrl t1  in
                     bind uu____8191
                       (fun res  ->
                          let uu____8214 = trivial ()  in
                          bind uu____8214 (fun uu____8222  -> ret res)))
                 in
              bind uu____8174
                (fun uu____8238  ->
                   match uu____8238 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8262 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8262 with
                          | (t2,lcomp,g) ->
                              let uu____8278 =
                                (let uu____8281 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8281) ||
                                  (let uu____8283 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8283)
                                 in
                              if uu____8278
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8298 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8298
                                   (fun uu____8318  ->
                                      match uu____8318 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8335  ->
                                                let uu____8336 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8337 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8336 uu____8337);
                                           (let uu____8338 =
                                              let uu____8341 =
                                                let uu____8342 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8342 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8341 opts
                                               in
                                            bind uu____8338
                                              (fun uu____8349  ->
                                                 let uu____8350 =
                                                   bind rewriter
                                                     (fun uu____8364  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8370  ->
                                                             let uu____8371 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8372 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8371
                                                               uu____8372);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8350)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____8420 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8420 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8457  ->
                     let uu____8458 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____8458);
                bind dismiss_all
                  (fun uu____8461  ->
                     let uu____8462 =
                       let uu____8469 = FStar_Tactics_Types.goal_env g  in
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts) uu____8469 keepGoing
                         gt1
                        in
                     bind uu____8462
                       (fun uu____8481  ->
                          match uu____8481 with
                          | (gt',uu____8489) ->
                              (log ps
                                 (fun uu____8493  ->
                                    let uu____8494 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____8494);
                               (let uu____8495 = push_goals gs  in
                                bind uu____8495
                                  (fun uu____8500  ->
                                     let uu____8501 =
                                       let uu____8504 =
                                         FStar_Tactics_Types.goal_with_type g
                                           gt'
                                          in
                                       [uu____8504]  in
                                     add_goals uu____8501)))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____8530 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8530 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8567  ->
                     let uu____8568 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____8568);
                bind dismiss_all
                  (fun uu____8571  ->
                     let uu____8572 =
                       let uu____8575 = FStar_Tactics_Types.goal_env g  in
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         uu____8575 gt1
                        in
                     bind uu____8572
                       (fun gt'  ->
                          log ps
                            (fun uu____8583  ->
                               let uu____8584 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____8584);
                          (let uu____8585 = push_goals gs  in
                           bind uu____8585
                             (fun uu____8590  ->
                                let uu____8591 =
                                  let uu____8594 =
                                    FStar_Tactics_Types.goal_with_type g gt'
                                     in
                                  [uu____8594]  in
                                add_goals uu____8591))))))
  
let (trefl : unit -> unit tac) =
  fun uu____8601  ->
    let uu____8604 = cur_goal ()  in
    bind uu____8604
      (fun g  ->
         let uu____8622 =
           let uu____8627 = FStar_Tactics_Types.goal_type g  in
           FStar_Syntax_Util.un_squash uu____8627  in
         match uu____8622 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8635 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8635 with
              | (hd1,args) ->
                  let uu____8668 =
                    let uu____8679 =
                      let uu____8680 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8680.FStar_Syntax_Syntax.n  in
                    (uu____8679, args)  in
                  (match uu____8668 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8692::(l,uu____8694)::(r,uu____8696)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8723 =
                         let uu____8726 = FStar_Tactics_Types.goal_env g  in
                         do_unify uu____8726 l r  in
                       bind uu____8723
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8733 =
                                let uu____8734 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8734 l  in
                              let uu____8735 =
                                let uu____8736 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8736 r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8733 uu____8735
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8739) ->
                       let uu____8752 =
                         let uu____8753 = FStar_Tactics_Types.goal_env g  in
                         tts uu____8753 t  in
                       fail1 "trefl: not an equality (%s)" uu____8752))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8762  ->
    let uu____8765 = cur_goal ()  in
    bind uu____8765
      (fun g  ->
         let uu____8771 =
           let uu____8778 = FStar_Tactics_Types.goal_env g  in
           let uu____8779 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8778 uu____8779  in
         bind uu____8771
           (fun uu____8788  ->
              match uu____8788 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___143_8798 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___143_8798.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___143_8798.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___143_8798.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8801  ->
                       let uu____8802 =
                         let uu____8805 = FStar_Tactics_Types.goal_env g  in
                         let uu____8806 =
                           let uu____8807 =
                             let uu____8808 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8809 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8808
                               uu____8809
                              in
                           let uu____8810 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8811 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8807 uu____8810 u
                             uu____8811
                            in
                         add_irrelevant_goal "dup equation" uu____8805
                           uu____8806 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8802
                         (fun uu____8814  ->
                            let uu____8815 = add_goals [g']  in
                            bind uu____8815 (fun uu____8819  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8826  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___144_8843 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___144_8843.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___144_8843.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___144_8843.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___144_8843.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___144_8843.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___144_8843.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___144_8843.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___144_8843.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___144_8843.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___144_8843.FStar_Tactics_Types.freshness)
                })
         | uu____8844 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8853  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___145_8866 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___145_8866.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___145_8866.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___145_8866.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___145_8866.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___145_8866.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___145_8866.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___145_8866.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___145_8866.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___145_8866.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___145_8866.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8873  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8880 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8900 =
      let uu____8907 = cur_goal ()  in
      bind uu____8907
        (fun g  ->
           let uu____8917 =
             let uu____8926 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8926 t  in
           bind uu____8917
             (fun uu____8954  ->
                match uu____8954 with
                | (t1,typ,guard) ->
                    let uu____8970 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8970 with
                     | (hd1,args) ->
                         let uu____9013 =
                           let uu____9026 =
                             let uu____9027 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9027.FStar_Syntax_Syntax.n  in
                           (uu____9026, args)  in
                         (match uu____9013 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9046)::(q,uu____9048)::[]) when
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
                                let uu____9086 =
                                  let uu____9087 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9087
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9086
                                 in
                              let g2 =
                                let uu____9089 =
                                  let uu____9090 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9090
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9089
                                 in
                              bind __dismiss
                                (fun uu____9097  ->
                                   let uu____9098 = add_goals [g1; g2]  in
                                   bind uu____9098
                                     (fun uu____9107  ->
                                        let uu____9108 =
                                          let uu____9113 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9114 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9113, uu____9114)  in
                                        ret uu____9108))
                          | uu____9119 ->
                              let uu____9132 =
                                let uu____9133 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9133 typ  in
                              fail1 "Not a disjunction: %s" uu____9132))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8900
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9163 = cur_goal ()  in
    bind uu____9163
      (fun g  ->
         FStar_Options.push ();
         (let uu____9176 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____9176);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___146_9183 = g  in
                 {
                   FStar_Tactics_Types.goal_main_env =
                     (uu___146_9183.FStar_Tactics_Types.goal_main_env);
                   FStar_Tactics_Types.goal_ctx_uvar =
                     (uu___146_9183.FStar_Tactics_Types.goal_ctx_uvar);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___146_9183.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____9191  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9204  ->
    let uu____9207 = cur_goal ()  in
    bind uu____9207
      (fun g  ->
         let uu____9213 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9213)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9222  ->
    let uu____9225 = cur_goal ()  in
    bind uu____9225
      (fun g  ->
         let uu____9231 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9231)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9240  ->
    let uu____9243 = cur_goal ()  in
    bind uu____9243
      (fun g  ->
         let uu____9249 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9249)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9266 =
        let uu____9269 = cur_goal ()  in
        bind uu____9269
          (fun goal  ->
             let env =
               let uu____9277 = FStar_Tactics_Types.goal_env goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____9277 ty  in
             let uu____9278 = __tc env tm  in
             bind uu____9278
               (fun uu____9298  ->
                  match uu____9298 with
                  | (tm1,typ,guard) ->
                      let uu____9310 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____9310 (fun uu____9314  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9266
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9337 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9343 =
              let uu____9350 =
                let uu____9351 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9351
                 in
              new_uvar "uvar_env.2" env uu____9350  in
            bind uu____9343
              (fun uu____9367  ->
                 match uu____9367 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9337
        (fun typ  ->
           let uu____9379 = new_uvar "uvar_env" env typ  in
           bind uu____9379
             (fun uu____9393  -> match uu____9393 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9411 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9430 -> g.FStar_Tactics_Types.opts
             | uu____9433 -> FStar_Options.peek ()  in
           let uu____9436 = FStar_Syntax_Util.head_and_args t  in
           match uu____9436 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9454);
                FStar_Syntax_Syntax.pos = uu____9455;
                FStar_Syntax_Syntax.vars = uu____9456;_},uu____9457)
               ->
               let env1 =
                 let uu___147_9499 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___147_9499.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___147_9499.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___147_9499.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___147_9499.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___147_9499.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___147_9499.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___147_9499.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___147_9499.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___147_9499.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___147_9499.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___147_9499.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___147_9499.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___147_9499.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___147_9499.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___147_9499.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___147_9499.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___147_9499.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___147_9499.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___147_9499.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___147_9499.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___147_9499.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___147_9499.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___147_9499.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___147_9499.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___147_9499.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___147_9499.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___147_9499.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___147_9499.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___147_9499.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___147_9499.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___147_9499.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___147_9499.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___147_9499.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___147_9499.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___147_9499.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___147_9499.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___147_9499.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let g1 =
                 let uu____9502 =
                   bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
                 FStar_Tactics_Types.goal_with_type g uu____9502  in
               add_goals [g1]
           | uu____9503 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9411
  
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
          (fun uu____9564  ->
             let uu____9565 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9565
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
        (fun uu____9586  ->
           let uu____9587 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9587)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9597 =
      mlog
        (fun uu____9602  ->
           let uu____9603 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9603)
        (fun uu____9606  ->
           let uu____9607 = cur_goal ()  in
           bind uu____9607
             (fun g  ->
                let uu____9613 =
                  let uu____9622 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9622 ty  in
                bind uu____9613
                  (fun uu____9634  ->
                     match uu____9634 with
                     | (ty1,uu____9644,guard) ->
                         let uu____9646 =
                           let uu____9649 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9649 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9646
                           (fun uu____9652  ->
                              let uu____9653 =
                                let uu____9656 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9657 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9656 uu____9657 ty1  in
                              bind uu____9653
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9663 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9663
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
                                        let uu____9669 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9670 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9669 uu____9670
                                         in
                                      let nty =
                                        let uu____9672 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9672 ty1  in
                                      let uu____9673 =
                                        let uu____9676 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9676 ng nty  in
                                      bind uu____9673
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9682 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9682
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9597
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9704::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9732 = init xs  in x :: uu____9732
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9749) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9806 = last args  in
        (match uu____9806 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9828 =
               let uu____9829 =
                 let uu____9834 =
                   let uu____9835 =
                     let uu____9840 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9840  in
                   uu____9835 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9834, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9829  in
             FStar_All.pipe_left ret uu____9828)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9851,uu____9852) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9896 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9896 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9929 =
                    let uu____9930 =
                      let uu____9935 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9935)  in
                    FStar_Reflection_Data.Tv_Abs uu____9930  in
                  FStar_All.pipe_left ret uu____9929))
    | FStar_Syntax_Syntax.Tm_type uu____9938 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9958 ->
        let uu____9971 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9971 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____10001 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____10001 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____10040 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____10048 =
          let uu____10049 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____10049  in
        FStar_All.pipe_left ret uu____10048
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
        let uu____10074 =
          let uu____10075 =
            let uu____10080 =
              let uu____10081 =
                FStar_Syntax_Unionfind.uvar_id
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_BigInt.of_int_fs uu____10081  in
            (uu____10080, (ctx_u, s))  in
          FStar_Reflection_Data.Tv_Uvar uu____10075  in
        FStar_All.pipe_left ret uu____10074
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____10117 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____10122 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____10122 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____10161 ->
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
           | FStar_Util.Inr uu____10191 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____10195 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____10195 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____10215 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____10219 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____10273 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____10273
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____10292 =
                let uu____10299 =
                  FStar_List.map
                    (fun uu____10311  ->
                       match uu____10311 with
                       | (p1,uu____10319) -> inspect_pat p1) ps
                   in
                (fv, uu____10299)  in
              FStar_Reflection_Data.Pat_Cons uu____10292
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
            (fun uu___91_10403  ->
               match uu___91_10403 with
               | (pat,uu____10421,t4) ->
                   let uu____10435 = inspect_pat pat  in (uu____10435, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____10442 ->
        ((let uu____10444 =
            let uu____10449 =
              let uu____10450 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____10451 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____10450
                uu____10451
               in
            (FStar_Errors.Warning_CantInspect, uu____10449)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10444);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10464 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10464
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10468 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10468
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10472 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10472
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10479 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10479
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10502 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10502
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10519 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10519
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10538 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10538
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10546 =
          let uu____10549 =
            let uu____10556 =
              let uu____10557 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10557  in
            FStar_Syntax_Syntax.mk uu____10556  in
          uu____10549 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10546
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10567 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10567
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10580 =
          let uu____10583 =
            let uu____10590 =
              let uu____10591 =
                let uu____10604 =
                  let uu____10607 =
                    let uu____10608 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10608]  in
                  FStar_Syntax_Subst.close uu____10607 t2  in
                ((false, [lb]), uu____10604)  in
              FStar_Syntax_Syntax.Tm_let uu____10591  in
            FStar_Syntax_Syntax.mk uu____10590  in
          uu____10583 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10580
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10644 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10644 with
         | (lbs,body) ->
             let uu____10659 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10659)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10697 =
                let uu____10698 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10698  in
              FStar_All.pipe_left wrap uu____10697
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10705 =
                let uu____10706 =
                  let uu____10719 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10735 = pack_pat p1  in
                         (uu____10735, false)) ps
                     in
                  (fv, uu____10719)  in
                FStar_Syntax_Syntax.Pat_cons uu____10706  in
              FStar_All.pipe_left wrap uu____10705
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
            (fun uu___92_10781  ->
               match uu___92_10781 with
               | (pat,t1) ->
                   let uu____10798 = pack_pat pat  in
                   (uu____10798, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10846 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10846
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10878 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10878
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10928 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10928
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10971 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10971
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10992 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10992 with
      | (u,ctx_uvars,g_u) ->
          let uu____11024 = FStar_List.hd ctx_uvars  in
          (match uu____11024 with
           | (ctx_uvar,uu____11038) ->
               let g =
                 let uu____11040 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11040 false
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
      let uu____11055 = goal_of_goal_ty env typ  in
      match uu____11055 with
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
          let uu____11071 = FStar_Tactics_Types.goal_witness g  in
          (ps, uu____11071)
  