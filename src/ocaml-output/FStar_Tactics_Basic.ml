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
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun goal  ->
    let uu____206 =
      FStar_Syntax_Unionfind.find
        (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
       in
    match uu____206 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____217 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____218 =
      let uu____219 = check_goal_solved g  in
      match uu____219 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____223 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____223
       in
    FStar_Util.format2 "%s%s" uu____217 uu____218
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____239 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____239
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____255 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____255
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____276 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____276
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____283) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____293) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____308 =
      let uu____313 =
        let uu____314 = FStar_Tactics_Types.goal_env g  in
        let uu____315 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____314 uu____315  in
      FStar_Syntax_Util.un_squash uu____313  in
    match uu____308 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____321 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____349 =
            let uu____350 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____350  in
          if uu____349 then tacprint msg else ());
         ret ())
  
let dump_goal : 'Auu____358 . 'Auu____358 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  -> let uu____370 = goal_to_string goal  in tacprint uu____370
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____382 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____386 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____386))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____395  ->
    match uu____395 with
    | (msg,ps) ->
        let uu____402 =
          let uu____405 =
            let uu____406 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____406 msg
             in
          let uu____407 =
            let uu____410 =
              let uu____411 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____411  in
            let uu____412 =
              let uu____415 =
                let uu____416 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____417 =
                  let uu____418 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____418  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____416
                  uu____417
                 in
              let uu____421 =
                let uu____424 =
                  let uu____425 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____426 =
                    let uu____427 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____427  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____425
                    uu____426
                   in
                [uu____424]  in
              uu____415 :: uu____421  in
            uu____410 :: uu____412  in
          uu____405 :: uu____407  in
        FStar_String.concat "" uu____402
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____436 =
        let uu____437 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____437  in
      let uu____438 =
        let uu____443 =
          let uu____444 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____444  in
        FStar_Syntax_Print.binders_to_json uu____443  in
      FStar_All.pipe_right uu____436 uu____438  in
    let uu____445 =
      let uu____452 =
        let uu____459 =
          let uu____464 =
            let uu____465 =
              let uu____472 =
                let uu____477 =
                  let uu____478 =
                    let uu____479 = FStar_Tactics_Types.goal_env g  in
                    let uu____480 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____479 uu____480  in
                  FStar_Util.JsonStr uu____478  in
                ("witness", uu____477)  in
              let uu____481 =
                let uu____488 =
                  let uu____493 =
                    let uu____494 =
                      let uu____495 = FStar_Tactics_Types.goal_env g  in
                      let uu____496 = FStar_Tactics_Types.goal_type g  in
                      tts uu____495 uu____496  in
                    FStar_Util.JsonStr uu____494  in
                  ("type", uu____493)  in
                [uu____488]  in
              uu____472 :: uu____481  in
            FStar_Util.JsonAssoc uu____465  in
          ("goal", uu____464)  in
        [uu____459]  in
      ("hyps", g_binders) :: uu____452  in
    FStar_Util.JsonAssoc uu____445
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____529  ->
    match uu____529 with
    | (msg,ps) ->
        let uu____536 =
          let uu____543 =
            let uu____550 =
              let uu____557 =
                let uu____564 =
                  let uu____569 =
                    let uu____570 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____570  in
                  ("goals", uu____569)  in
                let uu____573 =
                  let uu____580 =
                    let uu____585 =
                      let uu____586 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____586  in
                    ("smt-goals", uu____585)  in
                  [uu____580]  in
                uu____564 :: uu____573  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____557
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____550  in
          let uu____609 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____622 =
                let uu____627 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____627)  in
              [uu____622]
            else []  in
          FStar_List.append uu____543 uu____609  in
        FStar_Util.JsonAssoc uu____536
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____657  ->
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
         (let uu____680 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____680 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____698 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____698 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____731 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____731 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____762 =
              let uu____765 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____765  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____762);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____846 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____846
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____854 . Prims.string -> Prims.string -> 'Auu____854 tac =
  fun msg  ->
    fun x  -> let uu____867 = FStar_Util.format1 msg x  in fail uu____867
  
let fail2 :
  'Auu____876 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____876 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____894 = FStar_Util.format2 msg x y  in fail uu____894
  
let fail3 :
  'Auu____905 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____905 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____928 = FStar_Util.format3 msg x y z  in fail uu____928
  
let fail4 :
  'Auu____941 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____941 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____969 = FStar_Util.format4 msg x y z w  in fail uu____969
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1002 = run t ps  in
         match uu____1002 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___93_1026 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___93_1026.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___93_1026.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___93_1026.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___93_1026.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___93_1026.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___93_1026.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___93_1026.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___93_1026.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___93_1026.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___93_1026.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1053 = trytac' t  in
    bind uu____1053
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1080 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1116 = trytac t  in run uu____1116 ps
         with
         | FStar_Errors.Err (uu____1132,msg) ->
             (log ps
                (fun uu____1136  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1141,msg,uu____1143) ->
             (log ps
                (fun uu____1146  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1179 = run t ps  in
           match uu____1179 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1198  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1219 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1219
         then
           let uu____1220 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1221 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1220
             uu____1221
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1233 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1233
            then
              let uu____1234 = FStar_Util.string_of_bool res  in
              let uu____1235 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1236 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1234 uu____1235 uu____1236
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1244,msg) ->
             mlog
               (fun uu____1247  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1249  -> ret false)
         | FStar_Errors.Error (uu____1250,msg,r) ->
             mlog
               (fun uu____1255  ->
                  let uu____1256 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1256) (fun uu____1258  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1281  ->
             (let uu____1283 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1283
              then
                (FStar_Options.push ();
                 (let uu____1285 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1287 =
                let uu____1290 = __do_unify env t1 t2  in
                bind uu____1290
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
              bind uu____1287
                (fun r  ->
                   (let uu____1306 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1306 then FStar_Options.pop () else ());
                   ret r)))
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1322 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1322 with
      | FStar_Pervasives_Native.Some uu____1327 ->
          let uu____1328 =
            let uu____1329 = goal_to_string goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1329  in
          fail uu____1328
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1345 = FStar_Tactics_Types.goal_env goal  in
      let uu____1346 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1345 solution uu____1346
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1352 =
         let uu___98_1353 = p  in
         let uu____1354 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___98_1353.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___98_1353.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___98_1353.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1354;
           FStar_Tactics_Types.smt_goals =
             (uu___98_1353.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___98_1353.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___98_1353.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___98_1353.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___98_1353.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___98_1353.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___98_1353.FStar_Tactics_Types.freshness)
         }  in
       set uu____1352)
  
let (dismiss : unit -> unit tac) =
  fun uu____1363  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1370 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1387 = trysolve goal solution  in
      bind uu____1387
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1395 =
                let uu____1396 =
                  let uu____1397 = FStar_Tactics_Types.goal_env goal  in
                  tts uu____1397 solution  in
                let uu____1398 =
                  let uu____1399 = FStar_Tactics_Types.goal_env goal  in
                  let uu____1400 = FStar_Tactics_Types.goal_witness goal  in
                  tts uu____1399 uu____1400  in
                let uu____1401 =
                  let uu____1402 = FStar_Tactics_Types.goal_env goal  in
                  let uu____1403 = FStar_Tactics_Types.goal_type goal  in
                  tts uu____1402 uu____1403  in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1396
                  uu____1398 uu____1401
                 in
              fail uu____1395))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___99_1410 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___99_1410.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___99_1410.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___99_1410.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___99_1410.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___99_1410.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___99_1410.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___99_1410.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___99_1410.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___99_1410.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___99_1410.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1429 = FStar_Options.defensive ()  in
    if uu____1429
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1434 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1434)
         in
      let b2 =
        b1 &&
          (let uu____1437 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1437)
         in
      let rec aux b3 e =
        let uu____1449 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1449 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1467 =
        (let uu____1470 = aux b2 env  in Prims.op_Negation uu____1470) &&
          (let uu____1472 = FStar_ST.op_Bang nwarn  in
           uu____1472 < (Prims.parse_int "5"))
         in
      (if uu____1467
       then
         ((let uu____1497 =
             let uu____1498 = FStar_Tactics_Types.goal_type g  in
             uu____1498.FStar_Syntax_Syntax.pos  in
           let uu____1501 =
             let uu____1506 =
               let uu____1507 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1507
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1506)  in
           FStar_Errors.log_issue uu____1497 uu____1501);
          (let uu____1508 =
             let uu____1509 = FStar_ST.op_Bang nwarn  in
             uu____1509 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1508))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___100_1577 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___100_1577.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___100_1577.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___100_1577.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___100_1577.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___100_1577.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___100_1577.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___100_1577.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___100_1577.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___100_1577.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___100_1577.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___101_1597 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___101_1597.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___101_1597.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___101_1597.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___101_1597.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___101_1597.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___101_1597.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___101_1597.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___101_1597.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___101_1597.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___101_1597.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___102_1617 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___102_1617.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___102_1617.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___102_1617.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___102_1617.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___102_1617.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___102_1617.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___102_1617.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___102_1617.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___102_1617.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___102_1617.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___103_1637 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___103_1637.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___103_1637.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___103_1637.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___103_1637.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___103_1637.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___103_1637.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___103_1637.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___103_1637.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___103_1637.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___103_1637.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1648  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___104_1662 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___104_1662.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___104_1662.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___104_1662.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___104_1662.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___104_1662.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___104_1662.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___104_1662.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___104_1662.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___104_1662.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___104_1662.FStar_Tactics_Types.freshness)
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
        let uu____1700 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1700 with
        | (u,ctx_uvar,g_u) ->
            let uu____1734 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1734
              (fun uu____1743  ->
                 let uu____1744 =
                   let uu____1749 =
                     let uu____1750 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1750  in
                   (u, uu____1749)  in
                 ret uu____1744)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1768 = FStar_Syntax_Util.un_squash t  in
    match uu____1768 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1778 =
          let uu____1779 = FStar_Syntax_Subst.compress t'  in
          uu____1779.FStar_Syntax_Syntax.n  in
        (match uu____1778 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1783 -> false)
    | uu____1784 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1794 = FStar_Syntax_Util.un_squash t  in
    match uu____1794 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1804 =
          let uu____1805 = FStar_Syntax_Subst.compress t'  in
          uu____1805.FStar_Syntax_Syntax.n  in
        (match uu____1804 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1809 -> false)
    | uu____1810 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1821  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1832 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1832 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1839 = goal_to_string hd1  in
                    let uu____1840 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1839 uu____1840);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1847  ->
    let uu____1850 =
      let uu____1853 = cur_goal ()  in
      bind uu____1853
        (fun g  ->
           (let uu____1860 =
              let uu____1861 = FStar_Tactics_Types.goal_type g  in
              uu____1861.FStar_Syntax_Syntax.pos  in
            let uu____1864 =
              let uu____1869 =
                let uu____1870 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1870
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1869)  in
            FStar_Errors.log_issue uu____1860 uu____1864);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1850
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1881  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___105_1891 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___105_1891.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___105_1891.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___105_1891.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___105_1891.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___105_1891.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___105_1891.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___105_1891.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___105_1891.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___105_1891.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___105_1891.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1892 = set ps1  in
         bind uu____1892
           (fun uu____1897  ->
              let uu____1898 = FStar_BigInt.of_int_fs n1  in ret uu____1898))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1905  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1913 = FStar_BigInt.of_int_fs n1  in ret uu____1913)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1926  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1934 = FStar_BigInt.of_int_fs n1  in ret uu____1934)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1947  ->
    let uu____1950 = cur_goal ()  in
    bind uu____1950 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1982 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1982 phi  in
          let uu____1983 = new_uvar reason env typ  in
          bind uu____1983
            (fun uu____1998  ->
               match uu____1998 with
               | (uu____2005,ctx_uvar) ->
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
             (fun uu____2050  ->
                let uu____2051 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2051)
             (fun uu____2053  ->
                try
                  let uu____2073 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____2073
                with
                | FStar_Errors.Err (uu____2100,msg) ->
                    let uu____2102 = tts e t  in
                    let uu____2103 =
                      let uu____2104 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2104
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2102 uu____2103 msg
                | FStar_Errors.Error (uu____2111,msg,uu____2113) ->
                    let uu____2114 = tts e t  in
                    let uu____2115 =
                      let uu____2116 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2116
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2114 uu____2115 msg))
  
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
  fun uu____2143  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___108_2161 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___108_2161.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___108_2161.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___108_2161.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___108_2161.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___108_2161.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___108_2161.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___108_2161.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___108_2161.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___108_2161.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___108_2161.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2185 = get_guard_policy ()  in
      bind uu____2185
        (fun old_pol  ->
           let uu____2191 = set_guard_policy pol  in
           bind uu____2191
             (fun uu____2195  ->
                bind t
                  (fun r  ->
                     let uu____2199 = set_guard_policy old_pol  in
                     bind uu____2199 (fun uu____2203  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2228 =
            let uu____2229 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2229.FStar_TypeChecker_Env.guard_f  in
          match uu____2228 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2233 = istrivial e f  in
              if uu____2233
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2241 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2241
                           (fun goal  ->
                              let goal1 =
                                let uu___109_2248 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___109_2248.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___109_2248.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_2248.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2249 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2249
                           (fun goal  ->
                              let goal1 =
                                let uu___110_2256 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___110_2256.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___110_2256.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___110_2256.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2264 =
                              let uu____2265 =
                                let uu____2266 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2266
                                 in
                              Prims.op_Negation uu____2265  in
                            if uu____2264
                            then
                              mlog
                                (fun uu____2271  ->
                                   let uu____2272 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2272)
                                (fun uu____2274  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2281 ->
                              mlog
                                (fun uu____2284  ->
                                   let uu____2285 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2285)
                                (fun uu____2287  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2297 =
      let uu____2300 = cur_goal ()  in
      bind uu____2300
        (fun goal  ->
           let uu____2306 =
             let uu____2315 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2315 t  in
           bind uu____2306
             (fun uu____2327  ->
                match uu____2327 with
                | (t1,typ,guard) ->
                    let uu____2339 =
                      let uu____2342 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2342 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2339 (fun uu____2344  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2297
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2373 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2373 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2384  ->
    let uu____2387 = cur_goal ()  in
    bind uu____2387
      (fun goal  ->
         let uu____2393 =
           let uu____2394 = FStar_Tactics_Types.goal_env goal  in
           let uu____2395 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2394 uu____2395  in
         if uu____2393
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2399 =
              let uu____2400 = FStar_Tactics_Types.goal_env goal  in
              let uu____2401 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2400 uu____2401  in
            fail1 "Not a trivial goal: %s" uu____2399))
  
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
          let uu____2430 =
            let uu____2431 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2431.FStar_TypeChecker_Env.guard_f  in
          match uu____2430 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2439 = istrivial e f  in
              if uu____2439
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2447 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2447
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___113_2457 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___113_2457.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___113_2457.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___113_2457.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2464  ->
    let uu____2467 = cur_goal ()  in
    bind uu____2467
      (fun g  ->
         let uu____2473 = is_irrelevant g  in
         if uu____2473
         then bind __dismiss (fun uu____2477  -> add_smt_goals [g])
         else
           (let uu____2479 =
              let uu____2480 = FStar_Tactics_Types.goal_env g  in
              let uu____2481 = FStar_Tactics_Types.goal_type g  in
              tts uu____2480 uu____2481  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2479))
  
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
             let uu____2530 =
               try
                 let uu____2564 =
                   let uu____2573 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2573 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2564
               with | uu____2595 -> fail "divide: not enough goals"  in
             bind uu____2530
               (fun uu____2622  ->
                  match uu____2622 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___114_2648 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___114_2648.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___114_2648.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___114_2648.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___114_2648.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___114_2648.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___114_2648.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___114_2648.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___114_2648.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___114_2648.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___115_2650 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___115_2650.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___115_2650.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___115_2650.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___115_2650.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___115_2650.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___115_2650.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___115_2650.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___115_2650.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___115_2650.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2651 = set lp  in
                      bind uu____2651
                        (fun uu____2659  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2673 = set rp  in
                                     bind uu____2673
                                       (fun uu____2681  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___116_2697 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___116_2697.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___116_2697.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___116_2697.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___116_2697.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___116_2697.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___116_2697.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___116_2697.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___116_2697.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___116_2697.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2698 = set p'
                                                       in
                                                    bind uu____2698
                                                      (fun uu____2706  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2727 = divide FStar_BigInt.one f idtac  in
    bind uu____2727
      (fun uu____2740  -> match uu____2740 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2777::uu____2778 ->
             let uu____2781 =
               let uu____2790 = map tau  in
               divide FStar_BigInt.one tau uu____2790  in
             bind uu____2781
               (fun uu____2808  ->
                  match uu____2808 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2849 =
        bind t1
          (fun uu____2854  ->
             let uu____2855 = map t2  in
             bind uu____2855 (fun uu____2863  -> ret ()))
         in
      focus uu____2849
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2872  ->
    let uu____2875 =
      let uu____2878 = cur_goal ()  in
      bind uu____2878
        (fun goal  ->
           let uu____2887 =
             let uu____2894 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2894  in
           match uu____2887 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2903 =
                 let uu____2904 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2904  in
               if uu____2903
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2909 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2909 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2919 = new_uvar "intro" env' typ'  in
                  bind uu____2919
                    (fun uu____2935  ->
                       match uu____2935 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____2955 = set_solution goal sol  in
                           bind uu____2955
                             (fun uu____2961  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____2963 = replace_cur g  in
                                bind uu____2963 (fun uu____2967  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____2972 =
                 let uu____2973 = FStar_Tactics_Types.goal_env goal  in
                 let uu____2974 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____2973 uu____2974  in
               fail1 "goal is not an arrow (%s)" uu____2972)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2875
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2989  ->
    let uu____2996 = cur_goal ()  in
    bind uu____2996
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3013 =
            let uu____3020 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3020  in
          match uu____3013 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3033 =
                let uu____3034 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3034  in
              if uu____3033
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3047 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3047
                    in
                 let bs =
                   let uu____3055 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3055; b]  in
                 let env' =
                   let uu____3073 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3073 bs  in
                 let uu____3074 =
                   let uu____3081 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3081  in
                 bind uu____3074
                   (fun uu____3100  ->
                      match uu____3100 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3114 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3117 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3114
                              FStar_Parser_Const.effect_Tot_lid uu____3117 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3131 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3131 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3153 =
                                   let uu____3154 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3154.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3153
                                  in
                               let uu____3167 = set_solution goal tm  in
                               bind uu____3167
                                 (fun uu____3176  ->
                                    let uu____3177 =
                                      replace_cur
                                        (let uu___119_3182 = goal  in
                                         {
                                           FStar_Tactics_Types.goal_main_env
                                             =
                                             (uu___119_3182.FStar_Tactics_Types.goal_main_env);
                                           FStar_Tactics_Types.goal_ctx_uvar
                                             = ctx_uvar_u;
                                           FStar_Tactics_Types.opts =
                                             (uu___119_3182.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___119_3182.FStar_Tactics_Types.is_guard)
                                         })
                                       in
                                    bind uu____3177
                                      (fun uu____3189  ->
                                         let uu____3190 =
                                           let uu____3195 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3195, b)  in
                                         ret uu____3190)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3204 =
                let uu____3205 = FStar_Tactics_Types.goal_env goal  in
                let uu____3206 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3205 uu____3206  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3204))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3224 = cur_goal ()  in
    bind uu____3224
      (fun goal  ->
         mlog
           (fun uu____3231  ->
              let uu____3232 =
                let uu____3233 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3233  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3232)
           (fun uu____3238  ->
              let steps =
                let uu____3242 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3242
                 in
              let t =
                let uu____3246 = FStar_Tactics_Types.goal_env goal  in
                let uu____3247 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3246 uu____3247  in
              let uu____3248 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3248))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3272 =
          mlog
            (fun uu____3277  ->
               let uu____3278 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3278)
            (fun uu____3280  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3286 -> g.FStar_Tactics_Types.opts
                      | uu____3289 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3294  ->
                         let uu____3295 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3295)
                      (fun uu____3298  ->
                         let uu____3299 = __tc e t  in
                         bind uu____3299
                           (fun uu____3320  ->
                              match uu____3320 with
                              | (t1,uu____3330,uu____3331) ->
                                  let steps =
                                    let uu____3335 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3335
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3272
  
let (refine_intro : unit -> unit tac) =
  fun uu____3349  ->
    let uu____3352 =
      let uu____3355 = cur_goal ()  in
      bind uu____3355
        (fun g  ->
           let uu____3362 =
             let uu____3373 = FStar_Tactics_Types.goal_env g  in
             let uu____3374 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3373 uu____3374
              in
           match uu____3362 with
           | (uu____3377,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3402 =
                 let uu____3407 =
                   let uu____3412 =
                     let uu____3413 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3413]  in
                   FStar_Syntax_Subst.open_term uu____3412 phi  in
                 match uu____3407 with
                 | (bvs,phi1) ->
                     let uu____3432 =
                       let uu____3433 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3433  in
                     (uu____3432, phi1)
                  in
               (match uu____3402 with
                | (bv1,phi1) ->
                    let uu____3446 =
                      let uu____3449 = FStar_Tactics_Types.goal_env g  in
                      let uu____3450 =
                        let uu____3451 =
                          let uu____3454 =
                            let uu____3455 =
                              let uu____3462 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3462)  in
                            FStar_Syntax_Syntax.NT uu____3455  in
                          [uu____3454]  in
                        FStar_Syntax_Subst.subst uu____3451 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3449
                        uu____3450 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3446
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3470  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3352
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3489 = cur_goal ()  in
      bind uu____3489
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3497 = FStar_Tactics_Types.goal_env goal  in
               let uu____3498 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3497 uu____3498
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3500 = __tc env t  in
           bind uu____3500
             (fun uu____3519  ->
                match uu____3519 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3534  ->
                         let uu____3535 =
                           let uu____3536 = FStar_Tactics_Types.goal_env goal
                              in
                           tts uu____3536 typ  in
                         let uu____3537 =
                           let uu____3538 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3538
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3535 uu____3537)
                      (fun uu____3541  ->
                         let uu____3542 =
                           let uu____3545 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3545 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3542
                           (fun uu____3547  ->
                              mlog
                                (fun uu____3551  ->
                                   let uu____3552 =
                                     let uu____3553 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     tts uu____3553 typ  in
                                   let uu____3554 =
                                     let uu____3555 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3556 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     tts uu____3555 uu____3556  in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3552 uu____3554)
                                (fun uu____3559  ->
                                   let uu____3560 =
                                     let uu____3563 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3564 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3563 typ uu____3564  in
                                   bind uu____3560
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3570 =
                                             let uu____3571 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3571 t1  in
                                           let uu____3572 =
                                             let uu____3573 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3573 typ  in
                                           let uu____3574 =
                                             let uu____3575 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3576 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3575 uu____3576  in
                                           let uu____3577 =
                                             let uu____3578 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3579 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3578 uu____3579  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3570 uu____3572 uu____3574
                                             uu____3577)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3594 =
        mlog
          (fun uu____3599  ->
             let uu____3600 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3600)
          (fun uu____3603  ->
             let uu____3604 =
               let uu____3611 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3611  in
             bind uu____3604
               (fun uu___88_3620  ->
                  match uu___88_3620 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3629 =
                        let uu____3636 =
                          let uu____3639 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3639
                            (fun uu____3644  ->
                               let uu____3645 = refine_intro ()  in
                               bind uu____3645
                                 (fun uu____3649  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3636  in
                      bind uu____3629
                        (fun uu___87_3656  ->
                           match uu___87_3656 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3664 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3594
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3693 =
             let uu____3696 =
               let uu____3699 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3699  in
             FStar_Util.set_elements uu____3696  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3693
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
          let uu____3777 = f x  in
          bind uu____3777
            (fun y  ->
               let uu____3785 = mapM f xs  in
               bind uu____3785 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3805 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3825 = cur_goal ()  in
        bind uu____3825
          (fun goal  ->
             mlog
               (fun uu____3832  ->
                  let uu____3833 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3833)
               (fun uu____3836  ->
                  let uu____3837 =
                    let uu____3842 =
                      let uu____3845 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3845  in
                    trytac_exn uu____3842  in
                  bind uu____3837
                    (fun uu___89_3852  ->
                       match uu___89_3852 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3860  ->
                                let uu____3861 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3861)
                             (fun uu____3864  ->
                                let uu____3865 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3865 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3889  ->
                                         let uu____3890 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3890)
                                      (fun uu____3893  ->
                                         let uu____3894 =
                                           let uu____3895 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3895  in
                                         if uu____3894
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3899 =
                                              let uu____3906 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3906
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3899
                                              (fun uu____3917  ->
                                                 match uu____3917 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____3944 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____3944
                                                        in
                                                     let uu____3947 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____3947
                                                       (fun uu____3955  ->
                                                          let u1 =
                                                            let uu____3957 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____3957
                                                              u
                                                             in
                                                          let uu____3958 =
                                                            let uu____3959 =
                                                              let uu____3962
                                                                =
                                                                let uu____3963
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____3963
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____3962
                                                               in
                                                            uu____3959.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____3958
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____3991)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4015
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4015
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    add_goals
                                                                    [(
                                                                    let uu___120_4020
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___120_4020.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___120_4020.FStar_Tactics_Types.opts);
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
      let uu____4075 =
        mlog
          (fun uu____4080  ->
             let uu____4081 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4081)
          (fun uu____4084  ->
             let uu____4085 = cur_goal ()  in
             bind uu____4085
               (fun goal  ->
                  let uu____4091 =
                    let uu____4100 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4100 tm  in
                  bind uu____4091
                    (fun uu____4114  ->
                       match uu____4114 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4127 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4127 typ  in
                           let uu____4128 =
                             let uu____4131 =
                               let uu____4134 = __apply uopt tm1 typ1  in
                               bind uu____4134
                                 (fun uu____4139  ->
                                    let uu____4140 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4140 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4131  in
                           let uu____4141 =
                             let uu____4144 =
                               let uu____4145 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4145 tm1  in
                             let uu____4146 =
                               let uu____4147 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4147 typ1  in
                             let uu____4148 =
                               let uu____4149 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4150 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4149 uu____4150  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4144 uu____4146 uu____4148
                              in
                           try_unif uu____4128 uu____4141)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4075
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4173 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4173
    then
      let uu____4180 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4199 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4240 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4180 with
      | (pre,post) ->
          let post1 =
            let uu____4276 =
              let uu____4285 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4285]  in
            FStar_Syntax_Util.mk_app post uu____4276  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4309 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4309
       then
         let uu____4316 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4316
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4349 =
      let uu____4352 =
        mlog
          (fun uu____4357  ->
             let uu____4358 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4358)
          (fun uu____4362  ->
             let is_unit_t t =
               let uu____4369 =
                 let uu____4370 = FStar_Syntax_Subst.compress t  in
                 uu____4370.FStar_Syntax_Syntax.n  in
               match uu____4369 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4374 -> false  in
             let uu____4375 = cur_goal ()  in
             bind uu____4375
               (fun goal  ->
                  let uu____4381 =
                    let uu____4390 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4390 tm  in
                  bind uu____4381
                    (fun uu____4405  ->
                       match uu____4405 with
                       | (tm1,t,guard) ->
                           let uu____4417 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4417 with
                            | (bs,comp) ->
                                let uu____4444 = lemma_or_sq comp  in
                                (match uu____4444 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4463 =
                                       FStar_List.fold_left
                                         (fun uu____4505  ->
                                            fun uu____4506  ->
                                              match (uu____4505, uu____4506)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4597 =
                                                    is_unit_t b_t  in
                                                  if uu____4597
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4633 =
                                                       let uu____4646 =
                                                         let uu____4647 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4647.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4650 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4646
                                                         uu____4650 b_t
                                                        in
                                                     match uu____4633 with
                                                     | (u,uu____4666,g_u) ->
                                                         let uu____4680 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4680,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4463 with
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
                                          let uu____4741 =
                                            let uu____4744 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4745 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4746 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4744 uu____4745
                                              uu____4746
                                             in
                                          bind uu____4741
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4754 =
                                                   let uu____4755 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4755 tm1  in
                                                 let uu____4756 =
                                                   let uu____4757 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4758 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4757 uu____4758
                                                    in
                                                 let uu____4759 =
                                                   let uu____4760 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4761 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4760 uu____4761
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4754 uu____4756
                                                   uu____4759
                                               else
                                                 (let uu____4763 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4763
                                                    (fun uu____4768  ->
                                                       let uu____4769 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4769
                                                         (fun uu____4777  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4802
                                                                  =
                                                                  let uu____4805
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4805
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4802
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
                                                                   let uu____4840
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4840)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4856
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4856
                                                              with
                                                              | (hd1,uu____4872)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4894)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4915
                                                                    -> false)
                                                               in
                                                            let uu____4916 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4986
                                                                     ->
                                                                    match uu____4986
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range,uu____5011)
                                                                    ->
                                                                    let uu____5012
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5012
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5038)
                                                                    ->
                                                                    let uu____5059
                                                                    =
                                                                    let uu____5060
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5060.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5059
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5074)
                                                                    ->
                                                                    let env =
                                                                    let uu___123_5096
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___123_5096.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let goal_ty
                                                                    =
                                                                    bnorm env
                                                                    ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let goal1
                                                                    =
                                                                    FStar_Tactics_Types.goal_with_type
                                                                    (let uu___124_5101
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___124_5101.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___124_5101.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___124_5101.FStar_Tactics_Types.is_guard)
                                                                    })
                                                                    goal_ty
                                                                     in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5114
                                                                    ->
                                                                    let env =
                                                                    let uu___125_5116
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___125_5116.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5118
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5118
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
                                                                    let uu____5121
                                                                    =
                                                                    let uu____5128
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5128
                                                                    term1  in
                                                                    match uu____5121
                                                                    with
                                                                    | 
                                                                    (uu____5129,uu____5130,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5132
                                                                    =
                                                                    let uu____5137
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5137
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5132
                                                                    (fun
                                                                    uu___90_5149
                                                                     ->
                                                                    match uu___90_5149
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
                                                            bind uu____4916
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5217
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5217
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5239
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5239
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5300
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5300
                                                                    then
                                                                    let uu____5303
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5303
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
                                                                    let uu____5317
                                                                    =
                                                                    let uu____5318
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5318
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5317)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5319
                                                                   =
                                                                   let uu____5322
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5322
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5319
                                                                   (fun
                                                                    uu____5325
                                                                     ->
                                                                    let uu____5326
                                                                    =
                                                                    let uu____5329
                                                                    =
                                                                    let uu____5330
                                                                    =
                                                                    let uu____5331
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5332
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5331
                                                                    uu____5332
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5330
                                                                     in
                                                                    if
                                                                    uu____5329
                                                                    then
                                                                    let uu____5335
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5335
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5326
                                                                    (fun
                                                                    uu____5339
                                                                     ->
                                                                    let uu____5340
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5340
                                                                    (fun
                                                                    uu____5344
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4352  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4349
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5366 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5366 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5376::(e1,uu____5378)::(e2,uu____5380)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5423 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5447 = destruct_eq' typ  in
    match uu____5447 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5477 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5477 with
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
        let uu____5539 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5539 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5587 = aux e'  in
               FStar_Util.map_opt uu____5587
                 (fun uu____5611  ->
                    match uu____5611 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5632 = aux e  in
      FStar_Util.map_opt uu____5632
        (fun uu____5656  ->
           match uu____5656 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5723 =
            let uu____5732 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5732  in
          FStar_Util.map_opt uu____5723
            (fun uu____5747  ->
               match uu____5747 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___126_5766 = bv  in
                     let uu____5767 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___126_5766.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___126_5766.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5767
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___127_5775 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5776 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5783 =
                       let uu____5786 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5786  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___127_5775.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5776;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5783;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___127_5775.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___127_5775.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___127_5775.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___128_5787 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___128_5787.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___128_5787.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___128_5787.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5797 = cur_goal ()  in
    bind uu____5797
      (fun goal  ->
         let uu____5805 = h  in
         match uu____5805 with
         | (bv,uu____5809) ->
             mlog
               (fun uu____5813  ->
                  let uu____5814 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5815 =
                    let uu____5816 = FStar_Tactics_Types.goal_env goal  in
                    tts uu____5816 bv.FStar_Syntax_Syntax.sort  in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5814
                    uu____5815)
               (fun uu____5819  ->
                  let uu____5820 =
                    let uu____5829 = FStar_Tactics_Types.goal_env goal  in
                    split_env bv uu____5829  in
                  match uu____5820 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5850 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5850 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5865 =
                             let uu____5866 = FStar_Syntax_Subst.compress x
                                in
                             uu____5866.FStar_Syntax_Syntax.n  in
                           (match uu____5865 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___129_5883 = bv1  in
                                  let uu____5884 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___129_5883.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___129_5883.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5884
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let new_env = push_bvs e0 (bv :: bvs1)  in
                                let new_goal =
                                  let uu___130_5892 =
                                    goal.FStar_Tactics_Types.goal_ctx_uvar
                                     in
                                  let uu____5893 =
                                    FStar_TypeChecker_Env.all_binders new_env
                                     in
                                  let uu____5900 =
                                    let uu____5903 =
                                      FStar_Tactics_Types.goal_type goal  in
                                    FStar_Syntax_Subst.subst s uu____5903  in
                                  {
                                    FStar_Syntax_Syntax.ctx_uvar_head =
                                      (uu___130_5892.FStar_Syntax_Syntax.ctx_uvar_head);
                                    FStar_Syntax_Syntax.ctx_uvar_gamma =
                                      (new_env.FStar_TypeChecker_Env.gamma);
                                    FStar_Syntax_Syntax.ctx_uvar_binders =
                                      uu____5893;
                                    FStar_Syntax_Syntax.ctx_uvar_typ =
                                      uu____5900;
                                    FStar_Syntax_Syntax.ctx_uvar_reason =
                                      (uu___130_5892.FStar_Syntax_Syntax.ctx_uvar_reason);
                                    FStar_Syntax_Syntax.ctx_uvar_should_check
                                      =
                                      (uu___130_5892.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                    FStar_Syntax_Syntax.ctx_uvar_range =
                                      (uu___130_5892.FStar_Syntax_Syntax.ctx_uvar_range)
                                  }  in
                                replace_cur
                                  (let uu___131_5906 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___131_5906.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       new_goal;
                                     FStar_Tactics_Types.opts =
                                       (uu___131_5906.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___131_5906.FStar_Tactics_Types.is_guard)
                                   })
                            | uu____5907 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5908 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5929 = cur_goal ()  in
      bind uu____5929
        (fun goal  ->
           let uu____5940 = b  in
           match uu____5940 with
           | (bv,uu____5944) ->
               let bv' =
                 let uu____5946 =
                   let uu___132_5947 = bv  in
                   let uu____5948 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5948;
                     FStar_Syntax_Syntax.index =
                       (uu___132_5947.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___132_5947.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5946  in
               let s1 =
                 let uu____5952 =
                   let uu____5953 =
                     let uu____5960 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5960)  in
                   FStar_Syntax_Syntax.NT uu____5953  in
                 [uu____5952]  in
               let uu____5965 = subst_goal bv bv' s1 goal  in
               (match uu____5965 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5980 = cur_goal ()  in
    bind uu____5980
      (fun goal  ->
         let uu____5989 = b  in
         match uu____5989 with
         | (bv,uu____5993) ->
             let uu____5994 =
               let uu____6003 = FStar_Tactics_Types.goal_env goal  in
               split_env bv uu____6003  in
             (match uu____5994 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____6024 = FStar_Syntax_Util.type_u ()  in
                  (match uu____6024 with
                   | (ty,u) ->
                       let uu____6033 = new_uvar "binder_retype" e0 ty  in
                       bind uu____6033
                         (fun uu____6051  ->
                            match uu____6051 with
                            | (t',u_t') ->
                                let bv'' =
                                  let uu___133_6061 = bv  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___133_6061.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___133_6061.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t'
                                  }  in
                                let s =
                                  let uu____6065 =
                                    let uu____6066 =
                                      let uu____6073 =
                                        FStar_Syntax_Syntax.bv_to_name bv''
                                         in
                                      (bv, uu____6073)  in
                                    FStar_Syntax_Syntax.NT uu____6066  in
                                  [uu____6065]  in
                                let bvs1 =
                                  FStar_List.map
                                    (fun b1  ->
                                       let uu___134_6085 = b1  in
                                       let uu____6086 =
                                         FStar_Syntax_Subst.subst s
                                           b1.FStar_Syntax_Syntax.sort
                                          in
                                       {
                                         FStar_Syntax_Syntax.ppname =
                                           (uu___134_6085.FStar_Syntax_Syntax.ppname);
                                         FStar_Syntax_Syntax.index =
                                           (uu___134_6085.FStar_Syntax_Syntax.index);
                                         FStar_Syntax_Syntax.sort =
                                           uu____6086
                                       }) bvs
                                   in
                                let env' = push_bvs e0 (bv'' :: bvs1)  in
                                bind __dismiss
                                  (fun uu____6093  ->
                                     let new_goal =
                                       let uu____6095 =
                                         FStar_Tactics_Types.goal_with_env
                                           goal env'
                                          in
                                       let uu____6096 =
                                         let uu____6097 =
                                           FStar_Tactics_Types.goal_type goal
                                            in
                                         FStar_Syntax_Subst.subst s
                                           uu____6097
                                          in
                                       FStar_Tactics_Types.goal_with_type
                                         uu____6095 uu____6096
                                        in
                                     let uu____6098 = add_goals [new_goal]
                                        in
                                     bind uu____6098
                                       (fun uu____6103  ->
                                          let uu____6104 =
                                            FStar_Syntax_Util.mk_eq2
                                              (FStar_Syntax_Syntax.U_succ u)
                                              ty bv.FStar_Syntax_Syntax.sort
                                              t'
                                             in
                                          add_irrelevant_goal
                                            "binder_retype equation" e0
                                            uu____6104
                                            goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6123 = cur_goal ()  in
      bind uu____6123
        (fun goal  ->
           let uu____6132 = b  in
           match uu____6132 with
           | (bv,uu____6136) ->
               let uu____6137 =
                 let uu____6146 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6146  in
               (match uu____6137 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____6170 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____6170
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___135_6175 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___135_6175.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___135_6175.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    let uu____6177 =
                      FStar_Tactics_Types.goal_with_env goal env'  in
                    replace_cur uu____6177))
  
let (revert : unit -> unit tac) =
  fun uu____6184  ->
    let uu____6187 = cur_goal ()  in
    bind uu____6187
      (fun goal  ->
         let uu____6193 =
           let uu____6200 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6200  in
         match uu____6193 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6216 =
                 let uu____6219 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6219  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6216
                in
             let uu____6228 = new_uvar "revert" env' typ'  in
             bind uu____6228
               (fun uu____6243  ->
                  match uu____6243 with
                  | (r,u_r) ->
                      let uu____6252 =
                        let uu____6255 =
                          let uu____6256 =
                            let uu____6257 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6257.FStar_Syntax_Syntax.pos  in
                          let uu____6260 =
                            let uu____6265 =
                              let uu____6266 =
                                let uu____6273 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6273  in
                              [uu____6266]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6265  in
                          uu____6260 FStar_Pervasives_Native.None uu____6256
                           in
                        set_solution goal uu____6255  in
                      bind uu____6252
                        (fun uu____6290  ->
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
      let uu____6302 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6302
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6315 = cur_goal ()  in
    bind uu____6315
      (fun goal  ->
         mlog
           (fun uu____6323  ->
              let uu____6324 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6325 =
                let uu____6326 =
                  let uu____6327 =
                    let uu____6334 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6334  in
                  FStar_All.pipe_right uu____6327 FStar_List.length  in
                FStar_All.pipe_right uu____6326 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6324 uu____6325)
           (fun uu____6347  ->
              let uu____6348 =
                let uu____6357 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6357  in
              match uu____6348 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6396 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6396
                        then
                          let uu____6399 =
                            let uu____6400 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6400
                             in
                          fail uu____6399
                        else check1 bvs2
                     in
                  let uu____6402 =
                    let uu____6403 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6403  in
                  if uu____6402
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6407 = check1 bvs  in
                     bind uu____6407
                       (fun uu____6413  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6415 =
                            let uu____6422 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6422  in
                          bind uu____6415
                            (fun uu____6431  ->
                               match uu____6431 with
                               | (ut,uvar_ut) ->
                                   let uu____6440 = set_solution goal ut  in
                                   bind uu____6440
                                     (fun uu____6445  ->
                                        let uu____6446 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6446))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6453  ->
    let uu____6456 = cur_goal ()  in
    bind uu____6456
      (fun goal  ->
         let uu____6462 =
           let uu____6469 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6469  in
         match uu____6462 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6477) ->
             let uu____6482 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6482)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6492 = cur_goal ()  in
    bind uu____6492
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6502 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6502  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6505  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6515 = cur_goal ()  in
    bind uu____6515
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6525 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6525  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6528  -> add_goals [g']))
  
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
            let uu____6568 = FStar_Syntax_Subst.compress t  in
            uu____6568.FStar_Syntax_Syntax.n  in
          let uu____6571 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___139_6577 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___139_6577.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___139_6577.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6571
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6593 =
                   let uu____6594 = FStar_Syntax_Subst.compress t1  in
                   uu____6594.FStar_Syntax_Syntax.n  in
                 match uu____6593 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6621 = ff hd1  in
                     bind uu____6621
                       (fun hd2  ->
                          let fa uu____6643 =
                            match uu____6643 with
                            | (a,q) ->
                                let uu____6656 = ff a  in
                                bind uu____6656 (fun a1  -> ret (a1, q))
                             in
                          let uu____6669 = mapM fa args  in
                          bind uu____6669
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6735 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6735 with
                      | (bs1,t') ->
                          let uu____6744 =
                            let uu____6747 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6747 t'  in
                          bind uu____6744
                            (fun t''  ->
                               let uu____6751 =
                                 let uu____6752 =
                                   let uu____6769 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6776 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6769, uu____6776, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6752  in
                               ret uu____6751))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6845 = ff hd1  in
                     bind uu____6845
                       (fun hd2  ->
                          let ffb br =
                            let uu____6860 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6860 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6892 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6892  in
                                let uu____6893 = ff1 e  in
                                bind uu____6893
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6908 = mapM ffb brs  in
                          bind uu____6908
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6952;
                          FStar_Syntax_Syntax.lbtyp = uu____6953;
                          FStar_Syntax_Syntax.lbeff = uu____6954;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6956;
                          FStar_Syntax_Syntax.lbpos = uu____6957;_}::[]),e)
                     ->
                     let lb =
                       let uu____6982 =
                         let uu____6983 = FStar_Syntax_Subst.compress t1  in
                         uu____6983.FStar_Syntax_Syntax.n  in
                       match uu____6982 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6987) -> lb
                       | uu____7000 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7009 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7009
                         (fun def1  ->
                            ret
                              (let uu___136_7015 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___136_7015.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___136_7015.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___136_7015.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___136_7015.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___136_7015.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___136_7015.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7016 = fflb lb  in
                     bind uu____7016
                       (fun lb1  ->
                          let uu____7026 =
                            let uu____7031 =
                              let uu____7032 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7032]  in
                            FStar_Syntax_Subst.open_term uu____7031 e  in
                          match uu____7026 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7056 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7056  in
                              let uu____7057 = ff1 e1  in
                              bind uu____7057
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7098 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7098
                         (fun def  ->
                            ret
                              (let uu___137_7104 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___137_7104.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___137_7104.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___137_7104.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___137_7104.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___137_7104.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___137_7104.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7105 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7105 with
                      | (lbs1,e1) ->
                          let uu____7120 = mapM fflb lbs1  in
                          bind uu____7120
                            (fun lbs2  ->
                               let uu____7132 = ff e1  in
                               bind uu____7132
                                 (fun e2  ->
                                    let uu____7140 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7140 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7208 = ff t2  in
                     bind uu____7208
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7239 = ff t2  in
                     bind uu____7239
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7246 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___138_7253 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___138_7253.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___138_7253.FStar_Syntax_Syntax.vars)
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
            let uu____7290 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7290 with
            | (t1,lcomp,g) ->
                let uu____7302 =
                  (let uu____7305 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7305) ||
                    (let uu____7307 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7307)
                   in
                if uu____7302
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7317 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7317
                       (fun uu____7333  ->
                          match uu____7333 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7346  ->
                                    let uu____7347 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7348 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7347 uu____7348);
                               (let uu____7349 =
                                  let uu____7352 =
                                    let uu____7353 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7353 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7352
                                    opts
                                   in
                                bind uu____7349
                                  (fun uu____7356  ->
                                     let uu____7357 =
                                       bind tau
                                         (fun uu____7363  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7369  ->
                                                 let uu____7370 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7371 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7370 uu____7371);
                                            ret ut1)
                                        in
                                     focus uu____7357))))
                      in
                   let uu____7372 = trytac' rewrite_eq  in
                   bind uu____7372
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
          let uu____7570 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7570
            (fun t1  ->
               let uu____7578 =
                 f env
                   (let uu___142_7587 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___142_7587.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___142_7587.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7578
                 (fun uu____7603  ->
                    match uu____7603 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7626 =
                               let uu____7627 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7627.FStar_Syntax_Syntax.n  in
                             match uu____7626 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7660 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7660
                                   (fun uu____7685  ->
                                      match uu____7685 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7701 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7701
                                            (fun uu____7728  ->
                                               match uu____7728 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___140_7758 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___140_7758.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___140_7758.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7794 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7794 with
                                  | (bs1,t') ->
                                      let uu____7809 =
                                        let uu____7816 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7816 ctrl1 t'
                                         in
                                      bind uu____7809
                                        (fun uu____7834  ->
                                           match uu____7834 with
                                           | (t'',ctrl2) ->
                                               let uu____7849 =
                                                 let uu____7856 =
                                                   let uu___141_7859 = t4  in
                                                   let uu____7862 =
                                                     let uu____7863 =
                                                       let uu____7880 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7887 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7880,
                                                         uu____7887, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7863
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7862;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___141_7859.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___141_7859.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7856, ctrl2)  in
                                               ret uu____7849))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7934 -> ret (t3, ctrl1))))

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
              let uu____7977 = ctrl_tac_fold f env ctrl t  in
              bind uu____7977
                (fun uu____8001  ->
                   match uu____8001 with
                   | (t1,ctrl1) ->
                       let uu____8016 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8016
                         (fun uu____8043  ->
                            match uu____8043 with
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
              let uu____8125 =
                let uu____8132 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8132
                  (fun uu____8141  ->
                     let uu____8142 = ctrl t1  in
                     bind uu____8142
                       (fun res  ->
                          let uu____8165 = trivial ()  in
                          bind uu____8165 (fun uu____8173  -> ret res)))
                 in
              bind uu____8125
                (fun uu____8189  ->
                   match uu____8189 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8213 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8213 with
                          | (t2,lcomp,g) ->
                              let uu____8229 =
                                (let uu____8232 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8232) ||
                                  (let uu____8234 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8234)
                                 in
                              if uu____8229
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8249 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8249
                                   (fun uu____8269  ->
                                      match uu____8269 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8286  ->
                                                let uu____8287 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8288 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8287 uu____8288);
                                           (let uu____8289 =
                                              let uu____8292 =
                                                let uu____8293 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8293 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8292 opts
                                               in
                                            bind uu____8289
                                              (fun uu____8300  ->
                                                 let uu____8301 =
                                                   bind rewriter
                                                     (fun uu____8315  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8321  ->
                                                             let uu____8322 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8323 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8322
                                                               uu____8323);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8301)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____8371 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8371 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8408  ->
                     let uu____8409 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____8409);
                bind dismiss_all
                  (fun uu____8412  ->
                     let uu____8413 =
                       let uu____8420 = FStar_Tactics_Types.goal_env g  in
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts) uu____8420 keepGoing
                         gt1
                        in
                     bind uu____8413
                       (fun uu____8432  ->
                          match uu____8432 with
                          | (gt',uu____8440) ->
                              (log ps
                                 (fun uu____8444  ->
                                    let uu____8445 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____8445);
                               (let uu____8446 = push_goals gs  in
                                bind uu____8446
                                  (fun uu____8451  ->
                                     let uu____8452 =
                                       let uu____8455 =
                                         FStar_Tactics_Types.goal_with_type g
                                           gt'
                                          in
                                       [uu____8455]  in
                                     add_goals uu____8452)))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____8481 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8481 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8518  ->
                     let uu____8519 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____8519);
                bind dismiss_all
                  (fun uu____8522  ->
                     let uu____8523 =
                       let uu____8526 = FStar_Tactics_Types.goal_env g  in
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         uu____8526 gt1
                        in
                     bind uu____8523
                       (fun gt'  ->
                          log ps
                            (fun uu____8534  ->
                               let uu____8535 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____8535);
                          (let uu____8536 = push_goals gs  in
                           bind uu____8536
                             (fun uu____8541  ->
                                let uu____8542 =
                                  let uu____8545 =
                                    FStar_Tactics_Types.goal_with_type g gt'
                                     in
                                  [uu____8545]  in
                                add_goals uu____8542))))))
  
let (trefl : unit -> unit tac) =
  fun uu____8552  ->
    let uu____8555 = cur_goal ()  in
    bind uu____8555
      (fun g  ->
         let uu____8573 =
           let uu____8578 = FStar_Tactics_Types.goal_type g  in
           FStar_Syntax_Util.un_squash uu____8578  in
         match uu____8573 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8586 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8586 with
              | (hd1,args) ->
                  let uu____8619 =
                    let uu____8630 =
                      let uu____8631 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8631.FStar_Syntax_Syntax.n  in
                    (uu____8630, args)  in
                  (match uu____8619 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8643::(l,uu____8645)::(r,uu____8647)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8674 =
                         let uu____8677 = FStar_Tactics_Types.goal_env g  in
                         do_unify uu____8677 l r  in
                       bind uu____8674
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8684 =
                                let uu____8685 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8685 l  in
                              let uu____8686 =
                                let uu____8687 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8687 r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8684 uu____8686
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8690) ->
                       let uu____8703 =
                         let uu____8704 = FStar_Tactics_Types.goal_env g  in
                         tts uu____8704 t  in
                       fail1 "trefl: not an equality (%s)" uu____8703))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8713  ->
    let uu____8716 = cur_goal ()  in
    bind uu____8716
      (fun g  ->
         let uu____8722 =
           let uu____8729 = FStar_Tactics_Types.goal_env g  in
           let uu____8730 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8729 uu____8730  in
         bind uu____8722
           (fun uu____8739  ->
              match uu____8739 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___143_8749 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___143_8749.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___143_8749.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___143_8749.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8752  ->
                       let uu____8753 =
                         let uu____8756 = FStar_Tactics_Types.goal_env g  in
                         let uu____8757 =
                           let uu____8758 =
                             let uu____8759 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8760 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8759
                               uu____8760
                              in
                           let uu____8761 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8762 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8758 uu____8761 u
                             uu____8762
                            in
                         add_irrelevant_goal "dup equation" uu____8756
                           uu____8757 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8753
                         (fun uu____8765  ->
                            let uu____8766 = add_goals [g']  in
                            bind uu____8766 (fun uu____8770  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8777  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___144_8794 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___144_8794.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___144_8794.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___144_8794.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___144_8794.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___144_8794.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___144_8794.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___144_8794.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___144_8794.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___144_8794.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___144_8794.FStar_Tactics_Types.freshness)
                })
         | uu____8795 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8804  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___145_8817 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___145_8817.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___145_8817.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___145_8817.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___145_8817.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___145_8817.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___145_8817.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___145_8817.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___145_8817.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___145_8817.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___145_8817.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8824  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8831 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8851 =
      let uu____8858 = cur_goal ()  in
      bind uu____8858
        (fun g  ->
           let uu____8868 =
             let uu____8877 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8877 t  in
           bind uu____8868
             (fun uu____8905  ->
                match uu____8905 with
                | (t1,typ,guard) ->
                    let uu____8921 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8921 with
                     | (hd1,args) ->
                         let uu____8964 =
                           let uu____8977 =
                             let uu____8978 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8978.FStar_Syntax_Syntax.n  in
                           (uu____8977, args)  in
                         (match uu____8964 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8997)::(q,uu____8999)::[]) when
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
                                let uu____9037 =
                                  let uu____9038 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9038
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9037
                                 in
                              let g2 =
                                let uu____9040 =
                                  let uu____9041 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9041
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9040
                                 in
                              bind __dismiss
                                (fun uu____9048  ->
                                   let uu____9049 = add_goals [g1; g2]  in
                                   bind uu____9049
                                     (fun uu____9058  ->
                                        let uu____9059 =
                                          let uu____9064 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9065 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9064, uu____9065)  in
                                        ret uu____9059))
                          | uu____9070 ->
                              let uu____9083 =
                                let uu____9084 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9084 typ  in
                              fail1 "Not a disjunction: %s" uu____9083))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8851
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9114 = cur_goal ()  in
    bind uu____9114
      (fun g  ->
         FStar_Options.push ();
         (let uu____9127 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____9127);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___146_9134 = g  in
                 {
                   FStar_Tactics_Types.goal_main_env =
                     (uu___146_9134.FStar_Tactics_Types.goal_main_env);
                   FStar_Tactics_Types.goal_ctx_uvar =
                     (uu___146_9134.FStar_Tactics_Types.goal_ctx_uvar);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___146_9134.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____9142  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9155  ->
    let uu____9158 = cur_goal ()  in
    bind uu____9158
      (fun g  ->
         let uu____9164 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9164)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9173  ->
    let uu____9176 = cur_goal ()  in
    bind uu____9176
      (fun g  ->
         let uu____9182 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9182)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9191  ->
    let uu____9194 = cur_goal ()  in
    bind uu____9194
      (fun g  ->
         let uu____9200 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9200)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9217 =
        let uu____9220 = cur_goal ()  in
        bind uu____9220
          (fun goal  ->
             let env =
               let uu____9228 = FStar_Tactics_Types.goal_env goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____9228 ty  in
             let uu____9229 = __tc env tm  in
             bind uu____9229
               (fun uu____9249  ->
                  match uu____9249 with
                  | (tm1,typ,guard) ->
                      let uu____9261 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____9261 (fun uu____9265  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9217
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9288 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9294 =
              let uu____9301 =
                let uu____9302 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9302
                 in
              new_uvar "uvar_env.2" env uu____9301  in
            bind uu____9294
              (fun uu____9318  ->
                 match uu____9318 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9288
        (fun typ  ->
           let uu____9330 = new_uvar "uvar_env" env typ  in
           bind uu____9330
             (fun uu____9344  -> match uu____9344 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9362 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9381 -> g.FStar_Tactics_Types.opts
             | uu____9384 -> FStar_Options.peek ()  in
           let uu____9387 = FStar_Syntax_Util.head_and_args t  in
           match uu____9387 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9405);
                FStar_Syntax_Syntax.pos = uu____9406;
                FStar_Syntax_Syntax.vars = uu____9407;_},uu____9408)
               ->
               let env1 =
                 let uu___147_9450 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___147_9450.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___147_9450.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___147_9450.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___147_9450.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___147_9450.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___147_9450.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___147_9450.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___147_9450.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___147_9450.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___147_9450.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___147_9450.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___147_9450.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___147_9450.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___147_9450.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___147_9450.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___147_9450.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___147_9450.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___147_9450.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___147_9450.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___147_9450.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___147_9450.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___147_9450.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___147_9450.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___147_9450.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___147_9450.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___147_9450.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___147_9450.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___147_9450.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___147_9450.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___147_9450.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___147_9450.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___147_9450.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___147_9450.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___147_9450.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___147_9450.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___147_9450.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___147_9450.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let g1 =
                 let uu____9453 =
                   bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
                 FStar_Tactics_Types.goal_with_type g uu____9453  in
               add_goals [g1]
           | uu____9454 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9362
  
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
          (fun uu____9515  ->
             let uu____9516 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9516
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
        (fun uu____9537  ->
           let uu____9538 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9538)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9548 =
      mlog
        (fun uu____9553  ->
           let uu____9554 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9554)
        (fun uu____9557  ->
           let uu____9558 = cur_goal ()  in
           bind uu____9558
             (fun g  ->
                let uu____9564 =
                  let uu____9573 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9573 ty  in
                bind uu____9564
                  (fun uu____9585  ->
                     match uu____9585 with
                     | (ty1,uu____9595,guard) ->
                         let uu____9597 =
                           let uu____9600 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9600 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9597
                           (fun uu____9603  ->
                              let uu____9604 =
                                let uu____9607 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9608 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9607 uu____9608 ty1  in
                              bind uu____9604
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9614 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9614
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
                                        let uu____9620 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9621 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9620 uu____9621
                                         in
                                      let nty =
                                        let uu____9623 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9623 ty1  in
                                      let uu____9624 =
                                        let uu____9627 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9627 ng nty  in
                                      bind uu____9624
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9633 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9633
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9548
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9655::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9683 = init xs  in x :: uu____9683
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9700) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9757 = last args  in
        (match uu____9757 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9779 =
               let uu____9780 =
                 let uu____9785 =
                   let uu____9786 =
                     let uu____9791 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9791  in
                   uu____9786 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9785, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9780  in
             FStar_All.pipe_left ret uu____9779)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9802,uu____9803) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9847 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9847 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9880 =
                    let uu____9881 =
                      let uu____9886 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9886)  in
                    FStar_Reflection_Data.Tv_Abs uu____9881  in
                  FStar_All.pipe_left ret uu____9880))
    | FStar_Syntax_Syntax.Tm_type uu____9889 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9909 ->
        let uu____9922 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9922 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9952 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9952 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9991 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9999 =
          let uu____10000 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____10000  in
        FStar_All.pipe_left ret uu____9999
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,([],uu____10004)) ->
        let uu____10025 =
          let uu____10026 =
            let uu____10035 =
              let uu____10036 =
                FStar_Syntax_Unionfind.uvar_id
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_BigInt.of_int_fs uu____10036  in
            (uu____10035, (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ))
             in
          FStar_Reflection_Data.Tv_Uvar uu____10026  in
        FStar_All.pipe_left ret uu____10025
    | FStar_Syntax_Syntax.Tm_uvar uu____10039 ->
        failwith "NOT FULLY SUPPORTED"
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____10079 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____10084 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____10084 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____10123 ->
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
           | FStar_Util.Inr uu____10153 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____10157 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____10157 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____10177 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____10181 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____10235 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____10235
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____10254 =
                let uu____10261 =
                  FStar_List.map
                    (fun uu____10273  ->
                       match uu____10273 with
                       | (p1,uu____10281) -> inspect_pat p1) ps
                   in
                (fv, uu____10261)  in
              FStar_Reflection_Data.Pat_Cons uu____10254
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
            (fun uu___91_10365  ->
               match uu___91_10365 with
               | (pat,uu____10383,t4) ->
                   let uu____10397 = inspect_pat pat  in (uu____10397, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____10404 ->
        ((let uu____10406 =
            let uu____10411 =
              let uu____10412 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____10413 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____10412
                uu____10413
               in
            (FStar_Errors.Warning_CantInspect, uu____10411)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10406);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10426 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10426
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10430 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10430
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10434 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10434
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10441 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10441
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10464 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10464
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10481 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10481
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10500 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10500
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10508 =
          let uu____10511 =
            let uu____10518 =
              let uu____10519 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10519  in
            FStar_Syntax_Syntax.mk uu____10518  in
          uu____10511 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10508
    | FStar_Reflection_Data.Tv_Uvar (u,g,bs,t) ->
        let uu____10531 =
          let uu____10534 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____10534 (g, bs, t)  in
        FStar_All.pipe_left ret uu____10531
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10555 =
          let uu____10558 =
            let uu____10565 =
              let uu____10566 =
                let uu____10579 =
                  let uu____10582 =
                    let uu____10583 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10583]  in
                  FStar_Syntax_Subst.close uu____10582 t2  in
                ((false, [lb]), uu____10579)  in
              FStar_Syntax_Syntax.Tm_let uu____10566  in
            FStar_Syntax_Syntax.mk uu____10565  in
          uu____10558 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10555
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10619 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10619 with
         | (lbs,body) ->
             let uu____10634 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10634)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10672 =
                let uu____10673 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10673  in
              FStar_All.pipe_left wrap uu____10672
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10680 =
                let uu____10681 =
                  let uu____10694 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10710 = pack_pat p1  in
                         (uu____10710, false)) ps
                     in
                  (fv, uu____10694)  in
                FStar_Syntax_Syntax.Pat_cons uu____10681  in
              FStar_All.pipe_left wrap uu____10680
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
            (fun uu___92_10756  ->
               match uu___92_10756 with
               | (pat,t1) ->
                   let uu____10773 = pack_pat pat  in
                   (uu____10773, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10821 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10821
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10853 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10853
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10903 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10903
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10946 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10946
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10967 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10967 with
      | (u,ctx_uvars,g_u) ->
          let uu____10999 = FStar_List.hd ctx_uvars  in
          (match uu____10999 with
           | (ctx_uvar,uu____11013) ->
               let g =
                 let uu____11015 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11015 false
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
      let uu____11030 = goal_of_goal_ty env typ  in
      match uu____11030 with
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
          let uu____11046 = FStar_Tactics_Types.goal_witness g  in
          (ps, uu____11046)
  