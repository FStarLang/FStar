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
        let uu____1698 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1698 with
        | (u,ctx_uvar,g_u) ->
            let uu____1732 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1732
              (fun uu____1741  ->
                 let uu____1742 =
                   let uu____1747 =
                     let uu____1748 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1748  in
                   (u, uu____1747)  in
                 ret uu____1742)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1766 = FStar_Syntax_Util.un_squash t  in
    match uu____1766 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1776 =
          let uu____1777 = FStar_Syntax_Subst.compress t'  in
          uu____1777.FStar_Syntax_Syntax.n  in
        (match uu____1776 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1781 -> false)
    | uu____1782 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1792 = FStar_Syntax_Util.un_squash t  in
    match uu____1792 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1802 =
          let uu____1803 = FStar_Syntax_Subst.compress t'  in
          uu____1803.FStar_Syntax_Syntax.n  in
        (match uu____1802 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1807 -> false)
    | uu____1808 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1819  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1830 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1830 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1837 = goal_to_string hd1  in
                    let uu____1838 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1837 uu____1838);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1845  ->
    let uu____1848 =
      let uu____1851 = cur_goal ()  in
      bind uu____1851
        (fun g  ->
           (let uu____1858 =
              let uu____1859 = FStar_Tactics_Types.goal_type g  in
              uu____1859.FStar_Syntax_Syntax.pos  in
            let uu____1862 =
              let uu____1867 =
                let uu____1868 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1868
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1867)  in
            FStar_Errors.log_issue uu____1858 uu____1862);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1848
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1879  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___105_1889 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___105_1889.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___105_1889.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___105_1889.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___105_1889.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___105_1889.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___105_1889.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___105_1889.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___105_1889.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___105_1889.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___105_1889.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1890 = set ps1  in
         bind uu____1890
           (fun uu____1895  ->
              let uu____1896 = FStar_BigInt.of_int_fs n1  in ret uu____1896))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1903  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1911 = FStar_BigInt.of_int_fs n1  in ret uu____1911)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1924  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1932 = FStar_BigInt.of_int_fs n1  in ret uu____1932)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1945  ->
    let uu____1948 = cur_goal ()  in
    bind uu____1948 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1980 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1980 phi  in
          let uu____1981 = new_uvar reason env typ  in
          bind uu____1981
            (fun uu____1996  ->
               match uu____1996 with
               | (uu____2003,ctx_uvar) ->
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
             (fun uu____2048  ->
                let uu____2049 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2049)
             (fun uu____2052  ->
                let e1 =
                  let uu___106_2054 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___106_2054.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___106_2054.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___106_2054.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___106_2054.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___106_2054.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___106_2054.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___106_2054.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___106_2054.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___106_2054.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___106_2054.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___106_2054.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___106_2054.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___106_2054.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___106_2054.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___106_2054.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___106_2054.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___106_2054.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___106_2054.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___106_2054.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___106_2054.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___106_2054.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___106_2054.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___106_2054.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___106_2054.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___106_2054.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___106_2054.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___106_2054.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___106_2054.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___106_2054.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___106_2054.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___106_2054.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___106_2054.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___106_2054.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___106_2054.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___106_2054.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___106_2054.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___106_2054.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___106_2054.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2074 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2074
                with
                | FStar_Errors.Err (uu____2101,msg) ->
                    let uu____2103 = tts e1 t  in
                    let uu____2104 =
                      let uu____2105 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2105
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2103 uu____2104 msg
                | FStar_Errors.Error (uu____2112,msg,uu____2114) ->
                    let uu____2115 = tts e1 t  in
                    let uu____2116 =
                      let uu____2117 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2117
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2115 uu____2116 msg))
  
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
  fun uu____2144  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___109_2162 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___109_2162.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___109_2162.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___109_2162.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___109_2162.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___109_2162.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___109_2162.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___109_2162.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___109_2162.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___109_2162.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___109_2162.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2186 = get_guard_policy ()  in
      bind uu____2186
        (fun old_pol  ->
           let uu____2192 = set_guard_policy pol  in
           bind uu____2192
             (fun uu____2196  ->
                bind t
                  (fun r  ->
                     let uu____2200 = set_guard_policy old_pol  in
                     bind uu____2200 (fun uu____2204  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2229 =
            let uu____2230 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2230.FStar_TypeChecker_Env.guard_f  in
          match uu____2229 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2234 = istrivial e f  in
              if uu____2234
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2242 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2242
                           (fun goal  ->
                              let goal1 =
                                let uu___110_2249 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___110_2249.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___110_2249.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___110_2249.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2250 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2250
                           (fun goal  ->
                              let goal1 =
                                let uu___111_2257 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___111_2257.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___111_2257.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___111_2257.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2265 =
                              let uu____2266 =
                                let uu____2267 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2267
                                 in
                              Prims.op_Negation uu____2266  in
                            if uu____2265
                            then
                              mlog
                                (fun uu____2272  ->
                                   let uu____2273 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2273)
                                (fun uu____2275  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2282 ->
                              mlog
                                (fun uu____2285  ->
                                   let uu____2286 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2286)
                                (fun uu____2288  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2298 =
      let uu____2301 = cur_goal ()  in
      bind uu____2301
        (fun goal  ->
           let uu____2307 =
             let uu____2316 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2316 t  in
           bind uu____2307
             (fun uu____2328  ->
                match uu____2328 with
                | (t1,typ,guard) ->
                    let uu____2340 =
                      let uu____2343 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2343 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2340 (fun uu____2345  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2298
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2374 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2374 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2385  ->
    let uu____2388 = cur_goal ()  in
    bind uu____2388
      (fun goal  ->
         let uu____2394 =
           let uu____2395 = FStar_Tactics_Types.goal_env goal  in
           let uu____2396 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2395 uu____2396  in
         if uu____2394
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2400 =
              let uu____2401 = FStar_Tactics_Types.goal_env goal  in
              let uu____2402 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2401 uu____2402  in
            fail1 "Not a trivial goal: %s" uu____2400))
  
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
          let uu____2431 =
            let uu____2432 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2432.FStar_TypeChecker_Env.guard_f  in
          match uu____2431 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2440 = istrivial e f  in
              if uu____2440
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2448 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2448
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___114_2458 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___114_2458.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___114_2458.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___114_2458.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2465  ->
    let uu____2468 = cur_goal ()  in
    bind uu____2468
      (fun g  ->
         let uu____2474 = is_irrelevant g  in
         if uu____2474
         then bind __dismiss (fun uu____2478  -> add_smt_goals [g])
         else
           (let uu____2480 =
              let uu____2481 = FStar_Tactics_Types.goal_env g  in
              let uu____2482 = FStar_Tactics_Types.goal_type g  in
              tts uu____2481 uu____2482  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2480))
  
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
             let uu____2531 =
               try
                 let uu____2565 =
                   let uu____2574 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2574 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2565
               with | uu____2596 -> fail "divide: not enough goals"  in
             bind uu____2531
               (fun uu____2623  ->
                  match uu____2623 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___115_2649 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___115_2649.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___115_2649.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___115_2649.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___115_2649.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___115_2649.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___115_2649.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___115_2649.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___115_2649.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___115_2649.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___116_2651 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___116_2651.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___116_2651.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___116_2651.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___116_2651.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___116_2651.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___116_2651.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___116_2651.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___116_2651.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___116_2651.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2652 = set lp  in
                      bind uu____2652
                        (fun uu____2660  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2674 = set rp  in
                                     bind uu____2674
                                       (fun uu____2682  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___117_2698 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___117_2698.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___117_2698.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___117_2698.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___117_2698.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___117_2698.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___117_2698.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___117_2698.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___117_2698.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___117_2698.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2699 = set p'
                                                       in
                                                    bind uu____2699
                                                      (fun uu____2707  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2728 = divide FStar_BigInt.one f idtac  in
    bind uu____2728
      (fun uu____2741  -> match uu____2741 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2778::uu____2779 ->
             let uu____2782 =
               let uu____2791 = map tau  in
               divide FStar_BigInt.one tau uu____2791  in
             bind uu____2782
               (fun uu____2809  ->
                  match uu____2809 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2850 =
        bind t1
          (fun uu____2855  ->
             let uu____2856 = map t2  in
             bind uu____2856 (fun uu____2864  -> ret ()))
         in
      focus uu____2850
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2873  ->
    let uu____2876 =
      let uu____2879 = cur_goal ()  in
      bind uu____2879
        (fun goal  ->
           let uu____2888 =
             let uu____2895 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2895  in
           match uu____2888 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2904 =
                 let uu____2905 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2905  in
               if uu____2904
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2910 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2910 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2920 = new_uvar "intro" env' typ'  in
                  bind uu____2920
                    (fun uu____2936  ->
                       match uu____2936 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____2956 = set_solution goal sol  in
                           bind uu____2956
                             (fun uu____2962  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____2964 = replace_cur g  in
                                bind uu____2964 (fun uu____2968  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____2973 =
                 let uu____2974 = FStar_Tactics_Types.goal_env goal  in
                 let uu____2975 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____2974 uu____2975  in
               fail1 "goal is not an arrow (%s)" uu____2973)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2876
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2990  ->
    let uu____2997 = cur_goal ()  in
    bind uu____2997
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3014 =
            let uu____3021 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3021  in
          match uu____3014 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3034 =
                let uu____3035 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3035  in
              if uu____3034
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3048 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3048
                    in
                 let bs =
                   let uu____3056 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3056; b]  in
                 let env' =
                   let uu____3074 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3074 bs  in
                 let uu____3075 =
                   let uu____3082 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3082  in
                 bind uu____3075
                   (fun uu____3101  ->
                      match uu____3101 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3115 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3118 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3115
                              FStar_Parser_Const.effect_Tot_lid uu____3118 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3132 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3132 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3154 =
                                   let uu____3155 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3155.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3154
                                  in
                               let uu____3168 = set_solution goal tm  in
                               bind uu____3168
                                 (fun uu____3177  ->
                                    let uu____3178 =
                                      replace_cur
                                        (let uu___120_3183 = goal  in
                                         {
                                           FStar_Tactics_Types.goal_main_env
                                             =
                                             (uu___120_3183.FStar_Tactics_Types.goal_main_env);
                                           FStar_Tactics_Types.goal_ctx_uvar
                                             = ctx_uvar_u;
                                           FStar_Tactics_Types.opts =
                                             (uu___120_3183.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___120_3183.FStar_Tactics_Types.is_guard)
                                         })
                                       in
                                    bind uu____3178
                                      (fun uu____3190  ->
                                         let uu____3191 =
                                           let uu____3196 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3196, b)  in
                                         ret uu____3191)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3205 =
                let uu____3206 = FStar_Tactics_Types.goal_env goal  in
                let uu____3207 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3206 uu____3207  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3205))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3225 = cur_goal ()  in
    bind uu____3225
      (fun goal  ->
         mlog
           (fun uu____3232  ->
              let uu____3233 =
                let uu____3234 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3234  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3233)
           (fun uu____3239  ->
              let steps =
                let uu____3243 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3243
                 in
              let t =
                let uu____3247 = FStar_Tactics_Types.goal_env goal  in
                let uu____3248 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3247 uu____3248  in
              let uu____3249 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3249))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3273 =
          mlog
            (fun uu____3278  ->
               let uu____3279 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3279)
            (fun uu____3281  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3287 -> g.FStar_Tactics_Types.opts
                      | uu____3290 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3295  ->
                         let uu____3296 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3296)
                      (fun uu____3299  ->
                         let uu____3300 = __tc e t  in
                         bind uu____3300
                           (fun uu____3321  ->
                              match uu____3321 with
                              | (t1,uu____3331,uu____3332) ->
                                  let steps =
                                    let uu____3336 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3336
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3273
  
let (refine_intro : unit -> unit tac) =
  fun uu____3350  ->
    let uu____3353 =
      let uu____3356 = cur_goal ()  in
      bind uu____3356
        (fun g  ->
           let uu____3363 =
             let uu____3374 = FStar_Tactics_Types.goal_env g  in
             let uu____3375 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3374 uu____3375
              in
           match uu____3363 with
           | (uu____3378,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3403 =
                 let uu____3408 =
                   let uu____3413 =
                     let uu____3414 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3414]  in
                   FStar_Syntax_Subst.open_term uu____3413 phi  in
                 match uu____3408 with
                 | (bvs,phi1) ->
                     let uu____3433 =
                       let uu____3434 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3434  in
                     (uu____3433, phi1)
                  in
               (match uu____3403 with
                | (bv1,phi1) ->
                    let uu____3447 =
                      let uu____3450 = FStar_Tactics_Types.goal_env g  in
                      let uu____3451 =
                        let uu____3452 =
                          let uu____3455 =
                            let uu____3456 =
                              let uu____3463 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3463)  in
                            FStar_Syntax_Syntax.NT uu____3456  in
                          [uu____3455]  in
                        FStar_Syntax_Subst.subst uu____3452 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3450
                        uu____3451 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3447
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3471  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3353
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3490 = cur_goal ()  in
      bind uu____3490
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3498 = FStar_Tactics_Types.goal_env goal  in
               let uu____3499 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3498 uu____3499
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3501 = __tc env t  in
           bind uu____3501
             (fun uu____3520  ->
                match uu____3520 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3535  ->
                         let uu____3536 =
                           let uu____3537 = FStar_Tactics_Types.goal_env goal
                              in
                           tts uu____3537 typ  in
                         let uu____3538 =
                           let uu____3539 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3539
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3536 uu____3538)
                      (fun uu____3542  ->
                         let uu____3543 =
                           let uu____3546 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3546 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3543
                           (fun uu____3548  ->
                              mlog
                                (fun uu____3552  ->
                                   let uu____3553 =
                                     let uu____3554 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     tts uu____3554 typ  in
                                   let uu____3555 =
                                     let uu____3556 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3557 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     tts uu____3556 uu____3557  in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3553 uu____3555)
                                (fun uu____3560  ->
                                   let uu____3561 =
                                     let uu____3564 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3565 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3564 typ uu____3565  in
                                   bind uu____3561
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3571 =
                                             let uu____3572 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3572 t1  in
                                           let uu____3573 =
                                             let uu____3574 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3574 typ  in
                                           let uu____3575 =
                                             let uu____3576 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3577 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3576 uu____3577  in
                                           let uu____3578 =
                                             let uu____3579 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3580 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3579 uu____3580  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3571 uu____3573 uu____3575
                                             uu____3578)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3595 =
        mlog
          (fun uu____3600  ->
             let uu____3601 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3601)
          (fun uu____3604  ->
             let uu____3605 =
               let uu____3612 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3612  in
             bind uu____3605
               (fun uu___88_3621  ->
                  match uu___88_3621 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3630 =
                        let uu____3637 =
                          let uu____3640 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3640
                            (fun uu____3645  ->
                               let uu____3646 = refine_intro ()  in
                               bind uu____3646
                                 (fun uu____3650  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3637  in
                      bind uu____3630
                        (fun uu___87_3657  ->
                           match uu___87_3657 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3665 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3595
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3694 =
             let uu____3697 =
               let uu____3700 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3700  in
             FStar_Util.set_elements uu____3697  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3694
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
          let uu____3778 = f x  in
          bind uu____3778
            (fun y  ->
               let uu____3786 = mapM f xs  in
               bind uu____3786 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3806 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3826 = cur_goal ()  in
        bind uu____3826
          (fun goal  ->
             mlog
               (fun uu____3833  ->
                  let uu____3834 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3834)
               (fun uu____3837  ->
                  let uu____3838 =
                    let uu____3843 =
                      let uu____3846 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3846  in
                    trytac_exn uu____3843  in
                  bind uu____3838
                    (fun uu___89_3853  ->
                       match uu___89_3853 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3861  ->
                                let uu____3862 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3862)
                             (fun uu____3865  ->
                                let uu____3866 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3866 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3890  ->
                                         let uu____3891 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3891)
                                      (fun uu____3894  ->
                                         let uu____3895 =
                                           let uu____3896 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3896  in
                                         if uu____3895
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3900 =
                                              let uu____3907 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3907
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3900
                                              (fun uu____3918  ->
                                                 match uu____3918 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____3945 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____3945
                                                        in
                                                     let uu____3948 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____3948
                                                       (fun uu____3956  ->
                                                          let u1 =
                                                            let uu____3958 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____3958
                                                              u
                                                             in
                                                          let uu____3959 =
                                                            let uu____3960 =
                                                              let uu____3963
                                                                =
                                                                let uu____3964
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____3964
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____3963
                                                               in
                                                            uu____3960.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____3959
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____3992)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4016
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4016
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    add_goals
                                                                    [(
                                                                    let uu___121_4021
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___121_4021.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___121_4021.FStar_Tactics_Types.opts);
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
      let uu____4076 =
        mlog
          (fun uu____4081  ->
             let uu____4082 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4082)
          (fun uu____4085  ->
             let uu____4086 = cur_goal ()  in
             bind uu____4086
               (fun goal  ->
                  let uu____4092 =
                    let uu____4101 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4101 tm  in
                  bind uu____4092
                    (fun uu____4115  ->
                       match uu____4115 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4128 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4128 typ  in
                           let uu____4129 =
                             let uu____4132 =
                               let uu____4135 = __apply uopt tm1 typ1  in
                               bind uu____4135
                                 (fun uu____4140  ->
                                    let uu____4141 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4141 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4132  in
                           let uu____4142 =
                             let uu____4145 =
                               let uu____4146 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4146 tm1  in
                             let uu____4147 =
                               let uu____4148 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4148 typ1  in
                             let uu____4149 =
                               let uu____4150 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4151 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4150 uu____4151  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4145 uu____4147 uu____4149
                              in
                           try_unif uu____4129 uu____4142)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4076
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4174 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4174
    then
      let uu____4181 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4200 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4241 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4181 with
      | (pre,post) ->
          let post1 =
            let uu____4277 =
              let uu____4286 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4286]  in
            FStar_Syntax_Util.mk_app post uu____4277  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4310 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4310
       then
         let uu____4317 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4317
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4350 =
      let uu____4353 =
        mlog
          (fun uu____4358  ->
             let uu____4359 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4359)
          (fun uu____4363  ->
             let is_unit_t t =
               let uu____4370 =
                 let uu____4371 = FStar_Syntax_Subst.compress t  in
                 uu____4371.FStar_Syntax_Syntax.n  in
               match uu____4370 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4375 -> false  in
             let uu____4376 = cur_goal ()  in
             bind uu____4376
               (fun goal  ->
                  let uu____4382 =
                    let uu____4391 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4391 tm  in
                  bind uu____4382
                    (fun uu____4406  ->
                       match uu____4406 with
                       | (tm1,t,guard) ->
                           let uu____4418 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4418 with
                            | (bs,comp) ->
                                let uu____4445 = lemma_or_sq comp  in
                                (match uu____4445 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4464 =
                                       FStar_List.fold_left
                                         (fun uu____4506  ->
                                            fun uu____4507  ->
                                              match (uu____4506, uu____4507)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4598 =
                                                    is_unit_t b_t  in
                                                  if uu____4598
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4634 =
                                                       let uu____4647 =
                                                         let uu____4648 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4648.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4651 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4647
                                                         uu____4651 b_t
                                                        in
                                                     match uu____4634 with
                                                     | (u,uu____4667,g_u) ->
                                                         let uu____4681 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4681,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4464 with
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
                                          let uu____4742 =
                                            let uu____4745 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4746 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4747 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4745 uu____4746
                                              uu____4747
                                             in
                                          bind uu____4742
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4755 =
                                                   let uu____4756 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4756 tm1  in
                                                 let uu____4757 =
                                                   let uu____4758 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4759 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4758 uu____4759
                                                    in
                                                 let uu____4760 =
                                                   let uu____4761 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4762 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4761 uu____4762
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4755 uu____4757
                                                   uu____4760
                                               else
                                                 (let uu____4764 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4764
                                                    (fun uu____4769  ->
                                                       let uu____4770 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4770
                                                         (fun uu____4778  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4803
                                                                  =
                                                                  let uu____4806
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4806
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4803
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
                                                                   let uu____4841
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4841)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4857
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4857
                                                              with
                                                              | (hd1,uu____4873)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4895)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4916
                                                                    -> false)
                                                               in
                                                            let uu____4917 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4982
                                                                     ->
                                                                    match uu____4982
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5005
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5005
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5031)
                                                                    ->
                                                                    let uu____5052
                                                                    =
                                                                    let uu____5053
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5053.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5052
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5067)
                                                                    ->
                                                                    let env =
                                                                    let uu___124_5089
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___124_5089.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let goal_ty
                                                                    =
                                                                    bnorm env
                                                                    ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let goal1
                                                                    =
                                                                    FStar_Tactics_Types.goal_with_type
                                                                    (let uu___125_5094
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___125_5094.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___125_5094.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___125_5094.FStar_Tactics_Types.is_guard)
                                                                    })
                                                                    goal_ty
                                                                     in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5107
                                                                    ->
                                                                    let env =
                                                                    let uu___126_5109
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___126_5109.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5111
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5111
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
                                                                    let uu____5114
                                                                    =
                                                                    let uu____5121
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5121
                                                                    term1  in
                                                                    match uu____5114
                                                                    with
                                                                    | 
                                                                    (uu____5122,uu____5123,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5125
                                                                    =
                                                                    let uu____5130
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5130
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5125
                                                                    (fun
                                                                    uu___90_5142
                                                                     ->
                                                                    match uu___90_5142
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
                                                            bind uu____4917
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5210
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5210
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5232
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5232
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5293
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5293
                                                                    then
                                                                    let uu____5296
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5296
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
                                                                    let uu____5310
                                                                    =
                                                                    let uu____5311
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5311
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5310)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5312
                                                                   =
                                                                   let uu____5315
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5315
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5312
                                                                   (fun
                                                                    uu____5318
                                                                     ->
                                                                    let uu____5319
                                                                    =
                                                                    let uu____5322
                                                                    =
                                                                    let uu____5323
                                                                    =
                                                                    let uu____5324
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5325
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5324
                                                                    uu____5325
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5323
                                                                     in
                                                                    if
                                                                    uu____5322
                                                                    then
                                                                    let uu____5328
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5328
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5319
                                                                    (fun
                                                                    uu____5332
                                                                     ->
                                                                    let uu____5333
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5333
                                                                    (fun
                                                                    uu____5337
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4353  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4350
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5359 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5359 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5369::(e1,uu____5371)::(e2,uu____5373)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5416 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5440 = destruct_eq' typ  in
    match uu____5440 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5470 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5470 with
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
        let uu____5532 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5532 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5580 = aux e'  in
               FStar_Util.map_opt uu____5580
                 (fun uu____5604  ->
                    match uu____5604 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5625 = aux e  in
      FStar_Util.map_opt uu____5625
        (fun uu____5649  ->
           match uu____5649 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5716 =
            let uu____5725 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5725  in
          FStar_Util.map_opt uu____5716
            (fun uu____5740  ->
               match uu____5740 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___127_5759 = bv  in
                     let uu____5760 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___127_5759.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___127_5759.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5760
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___128_5768 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5769 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5776 =
                       let uu____5779 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5779  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___128_5768.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5769;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5776;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___128_5768.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___128_5768.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___128_5768.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___129_5780 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___129_5780.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___129_5780.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___129_5780.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5790 = cur_goal ()  in
    bind uu____5790
      (fun goal  ->
         let uu____5798 = h  in
         match uu____5798 with
         | (bv,uu____5802) ->
             mlog
               (fun uu____5806  ->
                  let uu____5807 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5808 =
                    let uu____5809 = FStar_Tactics_Types.goal_env goal  in
                    tts uu____5809 bv.FStar_Syntax_Syntax.sort  in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5807
                    uu____5808)
               (fun uu____5812  ->
                  let uu____5813 =
                    let uu____5822 = FStar_Tactics_Types.goal_env goal  in
                    split_env bv uu____5822  in
                  match uu____5813 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5843 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5843 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5858 =
                             let uu____5859 = FStar_Syntax_Subst.compress x
                                in
                             uu____5859.FStar_Syntax_Syntax.n  in
                           (match uu____5858 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___130_5876 = bv1  in
                                  let uu____5877 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___130_5876.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___130_5876.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5877
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let new_env = push_bvs e0 (bv :: bvs1)  in
                                let new_goal =
                                  let uu___131_5885 =
                                    goal.FStar_Tactics_Types.goal_ctx_uvar
                                     in
                                  let uu____5886 =
                                    FStar_TypeChecker_Env.all_binders new_env
                                     in
                                  let uu____5893 =
                                    let uu____5896 =
                                      FStar_Tactics_Types.goal_type goal  in
                                    FStar_Syntax_Subst.subst s uu____5896  in
                                  {
                                    FStar_Syntax_Syntax.ctx_uvar_head =
                                      (uu___131_5885.FStar_Syntax_Syntax.ctx_uvar_head);
                                    FStar_Syntax_Syntax.ctx_uvar_gamma =
                                      (new_env.FStar_TypeChecker_Env.gamma);
                                    FStar_Syntax_Syntax.ctx_uvar_binders =
                                      uu____5886;
                                    FStar_Syntax_Syntax.ctx_uvar_typ =
                                      uu____5893;
                                    FStar_Syntax_Syntax.ctx_uvar_reason =
                                      (uu___131_5885.FStar_Syntax_Syntax.ctx_uvar_reason);
                                    FStar_Syntax_Syntax.ctx_uvar_should_check
                                      =
                                      (uu___131_5885.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                    FStar_Syntax_Syntax.ctx_uvar_range =
                                      (uu___131_5885.FStar_Syntax_Syntax.ctx_uvar_range)
                                  }  in
                                replace_cur
                                  (let uu___132_5899 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___132_5899.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       new_goal;
                                     FStar_Tactics_Types.opts =
                                       (uu___132_5899.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___132_5899.FStar_Tactics_Types.is_guard)
                                   })
                            | uu____5900 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5901 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5922 = cur_goal ()  in
      bind uu____5922
        (fun goal  ->
           let uu____5933 = b  in
           match uu____5933 with
           | (bv,uu____5937) ->
               let bv' =
                 let uu____5939 =
                   let uu___133_5940 = bv  in
                   let uu____5941 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5941;
                     FStar_Syntax_Syntax.index =
                       (uu___133_5940.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___133_5940.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5939  in
               let s1 =
                 let uu____5945 =
                   let uu____5946 =
                     let uu____5953 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5953)  in
                   FStar_Syntax_Syntax.NT uu____5946  in
                 [uu____5945]  in
               let uu____5958 = subst_goal bv bv' s1 goal  in
               (match uu____5958 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5973 = cur_goal ()  in
    bind uu____5973
      (fun goal  ->
         let uu____5982 = b  in
         match uu____5982 with
         | (bv,uu____5986) ->
             let uu____5987 =
               let uu____5996 = FStar_Tactics_Types.goal_env goal  in
               split_env bv uu____5996  in
             (match uu____5987 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____6017 = FStar_Syntax_Util.type_u ()  in
                  (match uu____6017 with
                   | (ty,u) ->
                       let uu____6026 = new_uvar "binder_retype" e0 ty  in
                       bind uu____6026
                         (fun uu____6044  ->
                            match uu____6044 with
                            | (t',u_t') ->
                                let bv'' =
                                  let uu___134_6054 = bv  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___134_6054.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___134_6054.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t'
                                  }  in
                                let s =
                                  let uu____6058 =
                                    let uu____6059 =
                                      let uu____6066 =
                                        FStar_Syntax_Syntax.bv_to_name bv''
                                         in
                                      (bv, uu____6066)  in
                                    FStar_Syntax_Syntax.NT uu____6059  in
                                  [uu____6058]  in
                                let bvs1 =
                                  FStar_List.map
                                    (fun b1  ->
                                       let uu___135_6078 = b1  in
                                       let uu____6079 =
                                         FStar_Syntax_Subst.subst s
                                           b1.FStar_Syntax_Syntax.sort
                                          in
                                       {
                                         FStar_Syntax_Syntax.ppname =
                                           (uu___135_6078.FStar_Syntax_Syntax.ppname);
                                         FStar_Syntax_Syntax.index =
                                           (uu___135_6078.FStar_Syntax_Syntax.index);
                                         FStar_Syntax_Syntax.sort =
                                           uu____6079
                                       }) bvs
                                   in
                                let env' = push_bvs e0 (bv'' :: bvs1)  in
                                bind __dismiss
                                  (fun uu____6086  ->
                                     let new_goal =
                                       let uu____6088 =
                                         FStar_Tactics_Types.goal_with_env
                                           goal env'
                                          in
                                       let uu____6089 =
                                         let uu____6090 =
                                           FStar_Tactics_Types.goal_type goal
                                            in
                                         FStar_Syntax_Subst.subst s
                                           uu____6090
                                          in
                                       FStar_Tactics_Types.goal_with_type
                                         uu____6088 uu____6089
                                        in
                                     let uu____6091 = add_goals [new_goal]
                                        in
                                     bind uu____6091
                                       (fun uu____6096  ->
                                          let uu____6097 =
                                            FStar_Syntax_Util.mk_eq2
                                              (FStar_Syntax_Syntax.U_succ u)
                                              ty bv.FStar_Syntax_Syntax.sort
                                              t'
                                             in
                                          add_irrelevant_goal
                                            "binder_retype equation" e0
                                            uu____6097
                                            goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6116 = cur_goal ()  in
      bind uu____6116
        (fun goal  ->
           let uu____6125 = b  in
           match uu____6125 with
           | (bv,uu____6129) ->
               let uu____6130 =
                 let uu____6139 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6139  in
               (match uu____6130 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____6163 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____6163
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___136_6168 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___136_6168.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___136_6168.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    let uu____6170 =
                      FStar_Tactics_Types.goal_with_env goal env'  in
                    replace_cur uu____6170))
  
let (revert : unit -> unit tac) =
  fun uu____6177  ->
    let uu____6180 = cur_goal ()  in
    bind uu____6180
      (fun goal  ->
         let uu____6186 =
           let uu____6193 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6193  in
         match uu____6186 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6209 =
                 let uu____6212 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6212  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6209
                in
             let uu____6221 = new_uvar "revert" env' typ'  in
             bind uu____6221
               (fun uu____6236  ->
                  match uu____6236 with
                  | (r,u_r) ->
                      let uu____6245 =
                        let uu____6248 =
                          let uu____6249 =
                            let uu____6250 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6250.FStar_Syntax_Syntax.pos  in
                          let uu____6253 =
                            let uu____6258 =
                              let uu____6259 =
                                let uu____6266 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6266  in
                              [uu____6259]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6258  in
                          uu____6253 FStar_Pervasives_Native.None uu____6249
                           in
                        set_solution goal uu____6248  in
                      bind uu____6245
                        (fun uu____6283  ->
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
      let uu____6295 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6295
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6308 = cur_goal ()  in
    bind uu____6308
      (fun goal  ->
         mlog
           (fun uu____6316  ->
              let uu____6317 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6318 =
                let uu____6319 =
                  let uu____6320 =
                    let uu____6327 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6327  in
                  FStar_All.pipe_right uu____6320 FStar_List.length  in
                FStar_All.pipe_right uu____6319 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6317 uu____6318)
           (fun uu____6340  ->
              let uu____6341 =
                let uu____6350 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6350  in
              match uu____6341 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6389 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6389
                        then
                          let uu____6392 =
                            let uu____6393 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6393
                             in
                          fail uu____6392
                        else check1 bvs2
                     in
                  let uu____6395 =
                    let uu____6396 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6396  in
                  if uu____6395
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6400 = check1 bvs  in
                     bind uu____6400
                       (fun uu____6406  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6408 =
                            let uu____6415 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6415  in
                          bind uu____6408
                            (fun uu____6424  ->
                               match uu____6424 with
                               | (ut,uvar_ut) ->
                                   let uu____6433 = set_solution goal ut  in
                                   bind uu____6433
                                     (fun uu____6438  ->
                                        let uu____6439 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6439))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6446  ->
    let uu____6449 = cur_goal ()  in
    bind uu____6449
      (fun goal  ->
         let uu____6455 =
           let uu____6462 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6462  in
         match uu____6455 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6470) ->
             let uu____6475 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6475)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6485 = cur_goal ()  in
    bind uu____6485
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6495 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6495  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6498  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6508 = cur_goal ()  in
    bind uu____6508
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6518 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6518  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6521  -> add_goals [g']))
  
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
            let uu____6561 = FStar_Syntax_Subst.compress t  in
            uu____6561.FStar_Syntax_Syntax.n  in
          let uu____6564 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___140_6570 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___140_6570.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___140_6570.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6564
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6586 =
                   let uu____6587 = FStar_Syntax_Subst.compress t1  in
                   uu____6587.FStar_Syntax_Syntax.n  in
                 match uu____6586 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6614 = ff hd1  in
                     bind uu____6614
                       (fun hd2  ->
                          let fa uu____6636 =
                            match uu____6636 with
                            | (a,q) ->
                                let uu____6649 = ff a  in
                                bind uu____6649 (fun a1  -> ret (a1, q))
                             in
                          let uu____6662 = mapM fa args  in
                          bind uu____6662
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6728 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6728 with
                      | (bs1,t') ->
                          let uu____6737 =
                            let uu____6740 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6740 t'  in
                          bind uu____6737
                            (fun t''  ->
                               let uu____6744 =
                                 let uu____6745 =
                                   let uu____6762 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6769 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6762, uu____6769, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6745  in
                               ret uu____6744))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6838 = ff hd1  in
                     bind uu____6838
                       (fun hd2  ->
                          let ffb br =
                            let uu____6853 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6853 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6885 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6885  in
                                let uu____6886 = ff1 e  in
                                bind uu____6886
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6901 = mapM ffb brs  in
                          bind uu____6901
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6945;
                          FStar_Syntax_Syntax.lbtyp = uu____6946;
                          FStar_Syntax_Syntax.lbeff = uu____6947;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6949;
                          FStar_Syntax_Syntax.lbpos = uu____6950;_}::[]),e)
                     ->
                     let lb =
                       let uu____6975 =
                         let uu____6976 = FStar_Syntax_Subst.compress t1  in
                         uu____6976.FStar_Syntax_Syntax.n  in
                       match uu____6975 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6980) -> lb
                       | uu____6993 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7002 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7002
                         (fun def1  ->
                            ret
                              (let uu___137_7008 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___137_7008.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___137_7008.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___137_7008.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___137_7008.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___137_7008.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___137_7008.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7009 = fflb lb  in
                     bind uu____7009
                       (fun lb1  ->
                          let uu____7019 =
                            let uu____7024 =
                              let uu____7025 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7025]  in
                            FStar_Syntax_Subst.open_term uu____7024 e  in
                          match uu____7019 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7049 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7049  in
                              let uu____7050 = ff1 e1  in
                              bind uu____7050
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7091 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7091
                         (fun def  ->
                            ret
                              (let uu___138_7097 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___138_7097.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___138_7097.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___138_7097.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___138_7097.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___138_7097.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___138_7097.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7098 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7098 with
                      | (lbs1,e1) ->
                          let uu____7113 = mapM fflb lbs1  in
                          bind uu____7113
                            (fun lbs2  ->
                               let uu____7125 = ff e1  in
                               bind uu____7125
                                 (fun e2  ->
                                    let uu____7133 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7133 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7201 = ff t2  in
                     bind uu____7201
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7232 = ff t2  in
                     bind uu____7232
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7239 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___139_7246 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___139_7246.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___139_7246.FStar_Syntax_Syntax.vars)
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
            let uu____7283 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7283 with
            | (t1,lcomp,g) ->
                let uu____7295 =
                  (let uu____7298 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7298) ||
                    (let uu____7300 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7300)
                   in
                if uu____7295
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7310 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7310
                       (fun uu____7326  ->
                          match uu____7326 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7339  ->
                                    let uu____7340 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7341 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7340 uu____7341);
                               (let uu____7342 =
                                  let uu____7345 =
                                    let uu____7346 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7346 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7345
                                    opts
                                   in
                                bind uu____7342
                                  (fun uu____7349  ->
                                     let uu____7350 =
                                       bind tau
                                         (fun uu____7356  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7362  ->
                                                 let uu____7363 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7364 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7363 uu____7364);
                                            ret ut1)
                                        in
                                     focus uu____7350))))
                      in
                   let uu____7365 = trytac' rewrite_eq  in
                   bind uu____7365
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
          let uu____7563 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7563
            (fun t1  ->
               let uu____7571 =
                 f env
                   (let uu___143_7580 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___143_7580.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___143_7580.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7571
                 (fun uu____7596  ->
                    match uu____7596 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7619 =
                               let uu____7620 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7620.FStar_Syntax_Syntax.n  in
                             match uu____7619 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7653 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7653
                                   (fun uu____7678  ->
                                      match uu____7678 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7694 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7694
                                            (fun uu____7721  ->
                                               match uu____7721 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___141_7751 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___141_7751.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___141_7751.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7787 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7787 with
                                  | (bs1,t') ->
                                      let uu____7802 =
                                        let uu____7809 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7809 ctrl1 t'
                                         in
                                      bind uu____7802
                                        (fun uu____7827  ->
                                           match uu____7827 with
                                           | (t'',ctrl2) ->
                                               let uu____7842 =
                                                 let uu____7849 =
                                                   let uu___142_7852 = t4  in
                                                   let uu____7855 =
                                                     let uu____7856 =
                                                       let uu____7873 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7880 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7873,
                                                         uu____7880, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7856
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7855;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___142_7852.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___142_7852.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7849, ctrl2)  in
                                               ret uu____7842))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7927 -> ret (t3, ctrl1))))

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
              let uu____7970 = ctrl_tac_fold f env ctrl t  in
              bind uu____7970
                (fun uu____7994  ->
                   match uu____7994 with
                   | (t1,ctrl1) ->
                       let uu____8009 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8009
                         (fun uu____8036  ->
                            match uu____8036 with
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
              let uu____8118 =
                let uu____8125 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8125
                  (fun uu____8134  ->
                     let uu____8135 = ctrl t1  in
                     bind uu____8135
                       (fun res  ->
                          let uu____8158 = trivial ()  in
                          bind uu____8158 (fun uu____8166  -> ret res)))
                 in
              bind uu____8118
                (fun uu____8182  ->
                   match uu____8182 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8206 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8206 with
                          | (t2,lcomp,g) ->
                              let uu____8222 =
                                (let uu____8225 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8225) ||
                                  (let uu____8227 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8227)
                                 in
                              if uu____8222
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8242 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8242
                                   (fun uu____8262  ->
                                      match uu____8262 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8279  ->
                                                let uu____8280 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8281 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8280 uu____8281);
                                           (let uu____8282 =
                                              let uu____8285 =
                                                let uu____8286 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8286 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8285 opts
                                               in
                                            bind uu____8282
                                              (fun uu____8293  ->
                                                 let uu____8294 =
                                                   bind rewriter
                                                     (fun uu____8308  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8314  ->
                                                             let uu____8315 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8316 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8315
                                                               uu____8316);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8294)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____8364 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8364 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8401  ->
                     let uu____8402 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____8402);
                bind dismiss_all
                  (fun uu____8405  ->
                     let uu____8406 =
                       let uu____8413 = FStar_Tactics_Types.goal_env g  in
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts) uu____8413 keepGoing
                         gt1
                        in
                     bind uu____8406
                       (fun uu____8425  ->
                          match uu____8425 with
                          | (gt',uu____8433) ->
                              (log ps
                                 (fun uu____8437  ->
                                    let uu____8438 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____8438);
                               (let uu____8439 = push_goals gs  in
                                bind uu____8439
                                  (fun uu____8444  ->
                                     let uu____8445 =
                                       let uu____8448 =
                                         FStar_Tactics_Types.goal_with_type g
                                           gt'
                                          in
                                       [uu____8448]  in
                                     add_goals uu____8445)))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____8474 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8474 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8511  ->
                     let uu____8512 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____8512);
                bind dismiss_all
                  (fun uu____8515  ->
                     let uu____8516 =
                       let uu____8519 = FStar_Tactics_Types.goal_env g  in
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         uu____8519 gt1
                        in
                     bind uu____8516
                       (fun gt'  ->
                          log ps
                            (fun uu____8527  ->
                               let uu____8528 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____8528);
                          (let uu____8529 = push_goals gs  in
                           bind uu____8529
                             (fun uu____8534  ->
                                let uu____8535 =
                                  let uu____8538 =
                                    FStar_Tactics_Types.goal_with_type g gt'
                                     in
                                  [uu____8538]  in
                                add_goals uu____8535))))))
  
let (trefl : unit -> unit tac) =
  fun uu____8545  ->
    let uu____8548 = cur_goal ()  in
    bind uu____8548
      (fun g  ->
         let uu____8566 =
           let uu____8571 = FStar_Tactics_Types.goal_type g  in
           FStar_Syntax_Util.un_squash uu____8571  in
         match uu____8566 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8579 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8579 with
              | (hd1,args) ->
                  let uu____8612 =
                    let uu____8623 =
                      let uu____8624 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8624.FStar_Syntax_Syntax.n  in
                    (uu____8623, args)  in
                  (match uu____8612 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8636::(l,uu____8638)::(r,uu____8640)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8667 =
                         let uu____8670 = FStar_Tactics_Types.goal_env g  in
                         do_unify uu____8670 l r  in
                       bind uu____8667
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8677 =
                                let uu____8678 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8678 l  in
                              let uu____8679 =
                                let uu____8680 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8680 r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8677 uu____8679
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8683) ->
                       let uu____8696 =
                         let uu____8697 = FStar_Tactics_Types.goal_env g  in
                         tts uu____8697 t  in
                       fail1 "trefl: not an equality (%s)" uu____8696))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8706  ->
    let uu____8709 = cur_goal ()  in
    bind uu____8709
      (fun g  ->
         let uu____8715 =
           let uu____8722 = FStar_Tactics_Types.goal_env g  in
           let uu____8723 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8722 uu____8723  in
         bind uu____8715
           (fun uu____8732  ->
              match uu____8732 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___144_8742 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___144_8742.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___144_8742.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___144_8742.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8745  ->
                       let uu____8746 =
                         let uu____8749 = FStar_Tactics_Types.goal_env g  in
                         let uu____8750 =
                           let uu____8751 =
                             let uu____8752 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8753 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8752
                               uu____8753
                              in
                           let uu____8754 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8755 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8751 uu____8754 u
                             uu____8755
                            in
                         add_irrelevant_goal "dup equation" uu____8749
                           uu____8750 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8746
                         (fun uu____8758  ->
                            let uu____8759 = add_goals [g']  in
                            bind uu____8759 (fun uu____8763  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8770  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___145_8787 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___145_8787.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___145_8787.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___145_8787.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___145_8787.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___145_8787.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___145_8787.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___145_8787.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___145_8787.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___145_8787.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___145_8787.FStar_Tactics_Types.freshness)
                })
         | uu____8788 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8797  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___146_8810 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___146_8810.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___146_8810.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___146_8810.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___146_8810.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___146_8810.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___146_8810.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___146_8810.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___146_8810.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___146_8810.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___146_8810.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8817  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8824 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8844 =
      let uu____8851 = cur_goal ()  in
      bind uu____8851
        (fun g  ->
           let uu____8861 =
             let uu____8870 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8870 t  in
           bind uu____8861
             (fun uu____8898  ->
                match uu____8898 with
                | (t1,typ,guard) ->
                    let uu____8914 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8914 with
                     | (hd1,args) ->
                         let uu____8957 =
                           let uu____8970 =
                             let uu____8971 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8971.FStar_Syntax_Syntax.n  in
                           (uu____8970, args)  in
                         (match uu____8957 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8990)::(q,uu____8992)::[]) when
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
                                let uu____9030 =
                                  let uu____9031 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9031
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9030
                                 in
                              let g2 =
                                let uu____9033 =
                                  let uu____9034 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9034
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9033
                                 in
                              bind __dismiss
                                (fun uu____9041  ->
                                   let uu____9042 = add_goals [g1; g2]  in
                                   bind uu____9042
                                     (fun uu____9051  ->
                                        let uu____9052 =
                                          let uu____9057 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9058 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9057, uu____9058)  in
                                        ret uu____9052))
                          | uu____9063 ->
                              let uu____9076 =
                                let uu____9077 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9077 typ  in
                              fail1 "Not a disjunction: %s" uu____9076))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8844
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9107 = cur_goal ()  in
    bind uu____9107
      (fun g  ->
         FStar_Options.push ();
         (let uu____9120 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____9120);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___147_9127 = g  in
                 {
                   FStar_Tactics_Types.goal_main_env =
                     (uu___147_9127.FStar_Tactics_Types.goal_main_env);
                   FStar_Tactics_Types.goal_ctx_uvar =
                     (uu___147_9127.FStar_Tactics_Types.goal_ctx_uvar);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___147_9127.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____9135  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9148  ->
    let uu____9151 = cur_goal ()  in
    bind uu____9151
      (fun g  ->
         let uu____9157 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9157)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9166  ->
    let uu____9169 = cur_goal ()  in
    bind uu____9169
      (fun g  ->
         let uu____9175 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9175)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9184  ->
    let uu____9187 = cur_goal ()  in
    bind uu____9187
      (fun g  ->
         let uu____9193 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9193)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9210 =
        let uu____9213 = cur_goal ()  in
        bind uu____9213
          (fun goal  ->
             let env =
               let uu____9221 = FStar_Tactics_Types.goal_env goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____9221 ty  in
             let uu____9222 = __tc env tm  in
             bind uu____9222
               (fun uu____9242  ->
                  match uu____9242 with
                  | (tm1,typ,guard) ->
                      let uu____9254 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____9254 (fun uu____9258  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9210
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9281 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9287 =
              let uu____9294 =
                let uu____9295 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9295
                 in
              new_uvar "uvar_env.2" env uu____9294  in
            bind uu____9287
              (fun uu____9311  ->
                 match uu____9311 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9281
        (fun typ  ->
           let uu____9323 = new_uvar "uvar_env" env typ  in
           bind uu____9323
             (fun uu____9337  -> match uu____9337 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9355 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9374 -> g.FStar_Tactics_Types.opts
             | uu____9377 -> FStar_Options.peek ()  in
           let uu____9380 = FStar_Syntax_Util.head_and_args t  in
           match uu____9380 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9398);
                FStar_Syntax_Syntax.pos = uu____9399;
                FStar_Syntax_Syntax.vars = uu____9400;_},uu____9401)
               ->
               let env1 =
                 let uu___148_9443 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___148_9443.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___148_9443.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___148_9443.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___148_9443.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___148_9443.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___148_9443.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___148_9443.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___148_9443.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___148_9443.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___148_9443.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___148_9443.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___148_9443.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___148_9443.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___148_9443.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___148_9443.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___148_9443.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___148_9443.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___148_9443.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___148_9443.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___148_9443.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___148_9443.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___148_9443.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___148_9443.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___148_9443.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___148_9443.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___148_9443.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___148_9443.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___148_9443.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___148_9443.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___148_9443.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___148_9443.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___148_9443.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___148_9443.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___148_9443.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___148_9443.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___148_9443.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___148_9443.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___148_9443.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let g1 =
                 let uu____9446 =
                   bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
                 FStar_Tactics_Types.goal_with_type g uu____9446  in
               add_goals [g1]
           | uu____9447 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9355
  
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
          (fun uu____9508  ->
             let uu____9509 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9509
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
        (fun uu____9530  ->
           let uu____9531 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9531)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9541 =
      mlog
        (fun uu____9546  ->
           let uu____9547 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9547)
        (fun uu____9550  ->
           let uu____9551 = cur_goal ()  in
           bind uu____9551
             (fun g  ->
                let uu____9557 =
                  let uu____9566 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9566 ty  in
                bind uu____9557
                  (fun uu____9578  ->
                     match uu____9578 with
                     | (ty1,uu____9588,guard) ->
                         let uu____9590 =
                           let uu____9593 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9593 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9590
                           (fun uu____9596  ->
                              let uu____9597 =
                                let uu____9600 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9601 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9600 uu____9601 ty1  in
                              bind uu____9597
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9607 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9607
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
                                        let uu____9613 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9614 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9613 uu____9614
                                         in
                                      let nty =
                                        let uu____9616 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9616 ty1  in
                                      let uu____9617 =
                                        let uu____9620 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9620 ng nty  in
                                      bind uu____9617
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9626 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9626
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9541
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9648::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9676 = init xs  in x :: uu____9676
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9693) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9750 = last args  in
        (match uu____9750 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9772 =
               let uu____9773 =
                 let uu____9778 =
                   let uu____9779 =
                     let uu____9784 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9784  in
                   uu____9779 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9778, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9773  in
             FStar_All.pipe_left ret uu____9772)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9795,uu____9796) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9840 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9840 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9873 =
                    let uu____9874 =
                      let uu____9879 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9879)  in
                    FStar_Reflection_Data.Tv_Abs uu____9874  in
                  FStar_All.pipe_left ret uu____9873))
    | FStar_Syntax_Syntax.Tm_type uu____9882 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9902 ->
        let uu____9915 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9915 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9945 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9945 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9984 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9992 =
          let uu____9993 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____9993  in
        FStar_All.pipe_left ret uu____9992
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
        let uu____10018 =
          let uu____10019 =
            let uu____10024 =
              let uu____10025 =
                FStar_Syntax_Unionfind.uvar_id
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_BigInt.of_int_fs uu____10025  in
            (uu____10024, (ctx_u, s))  in
          FStar_Reflection_Data.Tv_Uvar uu____10019  in
        FStar_All.pipe_left ret uu____10018
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____10061 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____10066 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____10066 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____10105 ->
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
           | FStar_Util.Inr uu____10135 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____10139 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____10139 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____10159 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____10163 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____10217 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____10217
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____10236 =
                let uu____10243 =
                  FStar_List.map
                    (fun uu____10255  ->
                       match uu____10255 with
                       | (p1,uu____10263) -> inspect_pat p1) ps
                   in
                (fv, uu____10243)  in
              FStar_Reflection_Data.Pat_Cons uu____10236
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
            (fun uu___91_10347  ->
               match uu___91_10347 with
               | (pat,uu____10365,t4) ->
                   let uu____10379 = inspect_pat pat  in (uu____10379, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____10386 ->
        ((let uu____10388 =
            let uu____10393 =
              let uu____10394 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____10395 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____10394
                uu____10395
               in
            (FStar_Errors.Warning_CantInspect, uu____10393)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10388);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10408 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10408
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10412 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10412
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10416 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10416
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10423 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10423
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10446 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10446
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10463 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10463
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10482 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10482
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10490 =
          let uu____10493 =
            let uu____10500 =
              let uu____10501 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10501  in
            FStar_Syntax_Syntax.mk uu____10500  in
          uu____10493 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10490
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10511 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10511
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10524 =
          let uu____10527 =
            let uu____10534 =
              let uu____10535 =
                let uu____10548 =
                  let uu____10551 =
                    let uu____10552 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10552]  in
                  FStar_Syntax_Subst.close uu____10551 t2  in
                ((false, [lb]), uu____10548)  in
              FStar_Syntax_Syntax.Tm_let uu____10535  in
            FStar_Syntax_Syntax.mk uu____10534  in
          uu____10527 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10524
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10588 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10588 with
         | (lbs,body) ->
             let uu____10603 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10603)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10641 =
                let uu____10642 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10642  in
              FStar_All.pipe_left wrap uu____10641
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10649 =
                let uu____10650 =
                  let uu____10663 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10679 = pack_pat p1  in
                         (uu____10679, false)) ps
                     in
                  (fv, uu____10663)  in
                FStar_Syntax_Syntax.Pat_cons uu____10650  in
              FStar_All.pipe_left wrap uu____10649
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
            (fun uu___92_10725  ->
               match uu___92_10725 with
               | (pat,t1) ->
                   let uu____10742 = pack_pat pat  in
                   (uu____10742, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10790 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10790
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10822 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10822
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10872 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10872
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10915 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10915
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10936 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10936 with
      | (u,ctx_uvars,g_u) ->
          let uu____10968 = FStar_List.hd ctx_uvars  in
          (match uu____10968 with
           | (ctx_uvar,uu____10982) ->
               let g =
                 let uu____10984 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____10984 false
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
      let uu____10999 = goal_of_goal_ty env typ  in
      match uu____10999 with
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
          let uu____11015 = FStar_Tactics_Types.goal_witness g  in
          (ps, uu____11015)
  