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
             (fun uu____2051  ->
                try
                  let uu____2071 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____2071
                with
                | FStar_Errors.Err (uu____2098,msg) ->
                    let uu____2100 = tts e t  in
                    let uu____2101 =
                      let uu____2102 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2102
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2100 uu____2101 msg
                | FStar_Errors.Error (uu____2109,msg,uu____2111) ->
                    let uu____2112 = tts e t  in
                    let uu____2113 =
                      let uu____2114 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2114
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2112 uu____2113 msg))
  
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
  fun uu____2141  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___108_2159 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___108_2159.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___108_2159.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___108_2159.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___108_2159.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___108_2159.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___108_2159.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___108_2159.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___108_2159.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___108_2159.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___108_2159.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2183 = get_guard_policy ()  in
      bind uu____2183
        (fun old_pol  ->
           let uu____2189 = set_guard_policy pol  in
           bind uu____2189
             (fun uu____2193  ->
                bind t
                  (fun r  ->
                     let uu____2197 = set_guard_policy old_pol  in
                     bind uu____2197 (fun uu____2201  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2226 =
            let uu____2227 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2227.FStar_TypeChecker_Env.guard_f  in
          match uu____2226 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2231 = istrivial e f  in
              if uu____2231
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2239 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2239
                           (fun goal  ->
                              let goal1 =
                                let uu___109_2246 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___109_2246.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___109_2246.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_2246.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2247 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2247
                           (fun goal  ->
                              let goal1 =
                                let uu___110_2254 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___110_2254.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___110_2254.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___110_2254.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2262 =
                              let uu____2263 =
                                let uu____2264 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2264
                                 in
                              Prims.op_Negation uu____2263  in
                            if uu____2262
                            then
                              mlog
                                (fun uu____2269  ->
                                   let uu____2270 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2270)
                                (fun uu____2272  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2279 ->
                              mlog
                                (fun uu____2282  ->
                                   let uu____2283 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2283)
                                (fun uu____2285  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2295 =
      let uu____2298 = cur_goal ()  in
      bind uu____2298
        (fun goal  ->
           let uu____2304 =
             let uu____2313 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2313 t  in
           bind uu____2304
             (fun uu____2325  ->
                match uu____2325 with
                | (t1,typ,guard) ->
                    let uu____2337 =
                      let uu____2340 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2340 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2337 (fun uu____2342  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2295
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2371 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2371 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2382  ->
    let uu____2385 = cur_goal ()  in
    bind uu____2385
      (fun goal  ->
         let uu____2391 =
           let uu____2392 = FStar_Tactics_Types.goal_env goal  in
           let uu____2393 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2392 uu____2393  in
         if uu____2391
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2397 =
              let uu____2398 = FStar_Tactics_Types.goal_env goal  in
              let uu____2399 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2398 uu____2399  in
            fail1 "Not a trivial goal: %s" uu____2397))
  
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
          let uu____2428 =
            let uu____2429 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2429.FStar_TypeChecker_Env.guard_f  in
          match uu____2428 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2437 = istrivial e f  in
              if uu____2437
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2445 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2445
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___113_2455 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___113_2455.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___113_2455.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___113_2455.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2462  ->
    let uu____2465 = cur_goal ()  in
    bind uu____2465
      (fun g  ->
         let uu____2471 = is_irrelevant g  in
         if uu____2471
         then bind __dismiss (fun uu____2475  -> add_smt_goals [g])
         else
           (let uu____2477 =
              let uu____2478 = FStar_Tactics_Types.goal_env g  in
              let uu____2479 = FStar_Tactics_Types.goal_type g  in
              tts uu____2478 uu____2479  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2477))
  
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
             let uu____2528 =
               try
                 let uu____2562 =
                   let uu____2571 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2571 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2562
               with | uu____2593 -> fail "divide: not enough goals"  in
             bind uu____2528
               (fun uu____2620  ->
                  match uu____2620 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___114_2646 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___114_2646.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___114_2646.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___114_2646.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___114_2646.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___114_2646.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___114_2646.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___114_2646.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___114_2646.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___114_2646.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___115_2648 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___115_2648.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___115_2648.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___115_2648.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___115_2648.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___115_2648.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___115_2648.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___115_2648.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___115_2648.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___115_2648.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2649 = set lp  in
                      bind uu____2649
                        (fun uu____2657  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2671 = set rp  in
                                     bind uu____2671
                                       (fun uu____2679  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___116_2695 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___116_2695.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___116_2695.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___116_2695.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___116_2695.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___116_2695.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___116_2695.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___116_2695.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___116_2695.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___116_2695.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2696 = set p'
                                                       in
                                                    bind uu____2696
                                                      (fun uu____2704  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2725 = divide FStar_BigInt.one f idtac  in
    bind uu____2725
      (fun uu____2738  -> match uu____2738 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2775::uu____2776 ->
             let uu____2779 =
               let uu____2788 = map tau  in
               divide FStar_BigInt.one tau uu____2788  in
             bind uu____2779
               (fun uu____2806  ->
                  match uu____2806 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2847 =
        bind t1
          (fun uu____2852  ->
             let uu____2853 = map t2  in
             bind uu____2853 (fun uu____2861  -> ret ()))
         in
      focus uu____2847
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2870  ->
    let uu____2873 =
      let uu____2876 = cur_goal ()  in
      bind uu____2876
        (fun goal  ->
           let uu____2885 =
             let uu____2892 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2892  in
           match uu____2885 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2901 =
                 let uu____2902 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2902  in
               if uu____2901
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2907 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2907 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2917 = new_uvar "intro" env' typ'  in
                  bind uu____2917
                    (fun uu____2933  ->
                       match uu____2933 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____2953 = set_solution goal sol  in
                           bind uu____2953
                             (fun uu____2959  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____2961 = replace_cur g  in
                                bind uu____2961 (fun uu____2965  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____2970 =
                 let uu____2971 = FStar_Tactics_Types.goal_env goal  in
                 let uu____2972 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____2971 uu____2972  in
               fail1 "goal is not an arrow (%s)" uu____2970)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2873
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2987  ->
    let uu____2994 = cur_goal ()  in
    bind uu____2994
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3011 =
            let uu____3018 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3018  in
          match uu____3011 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3031 =
                let uu____3032 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3032  in
              if uu____3031
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3045 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3045
                    in
                 let bs =
                   let uu____3053 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3053; b]  in
                 let env' =
                   let uu____3071 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3071 bs  in
                 let uu____3072 =
                   let uu____3079 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3079  in
                 bind uu____3072
                   (fun uu____3098  ->
                      match uu____3098 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3112 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3115 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3112
                              FStar_Parser_Const.effect_Tot_lid uu____3115 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3129 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3129 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3151 =
                                   let uu____3152 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3152.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3151
                                  in
                               let uu____3165 = set_solution goal tm  in
                               bind uu____3165
                                 (fun uu____3174  ->
                                    let uu____3175 =
                                      replace_cur
                                        (let uu___119_3180 = goal  in
                                         {
                                           FStar_Tactics_Types.goal_main_env
                                             =
                                             (uu___119_3180.FStar_Tactics_Types.goal_main_env);
                                           FStar_Tactics_Types.goal_ctx_uvar
                                             = ctx_uvar_u;
                                           FStar_Tactics_Types.opts =
                                             (uu___119_3180.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___119_3180.FStar_Tactics_Types.is_guard)
                                         })
                                       in
                                    bind uu____3175
                                      (fun uu____3187  ->
                                         let uu____3188 =
                                           let uu____3193 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3193, b)  in
                                         ret uu____3188)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3202 =
                let uu____3203 = FStar_Tactics_Types.goal_env goal  in
                let uu____3204 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3203 uu____3204  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3202))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3222 = cur_goal ()  in
    bind uu____3222
      (fun goal  ->
         mlog
           (fun uu____3229  ->
              let uu____3230 =
                let uu____3231 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3231  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3230)
           (fun uu____3236  ->
              let steps =
                let uu____3240 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3240
                 in
              let t =
                let uu____3244 = FStar_Tactics_Types.goal_env goal  in
                let uu____3245 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3244 uu____3245  in
              let uu____3246 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3246))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3270 =
          mlog
            (fun uu____3275  ->
               let uu____3276 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3276)
            (fun uu____3278  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3284 -> g.FStar_Tactics_Types.opts
                      | uu____3287 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3292  ->
                         let uu____3293 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3293)
                      (fun uu____3296  ->
                         let uu____3297 = __tc e t  in
                         bind uu____3297
                           (fun uu____3318  ->
                              match uu____3318 with
                              | (t1,uu____3328,uu____3329) ->
                                  let steps =
                                    let uu____3333 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3333
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3270
  
let (refine_intro : unit -> unit tac) =
  fun uu____3347  ->
    let uu____3350 =
      let uu____3353 = cur_goal ()  in
      bind uu____3353
        (fun g  ->
           let uu____3360 =
             let uu____3371 = FStar_Tactics_Types.goal_env g  in
             let uu____3372 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3371 uu____3372
              in
           match uu____3360 with
           | (uu____3375,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3400 =
                 let uu____3405 =
                   let uu____3410 =
                     let uu____3411 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3411]  in
                   FStar_Syntax_Subst.open_term uu____3410 phi  in
                 match uu____3405 with
                 | (bvs,phi1) ->
                     let uu____3430 =
                       let uu____3431 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3431  in
                     (uu____3430, phi1)
                  in
               (match uu____3400 with
                | (bv1,phi1) ->
                    let uu____3444 =
                      let uu____3447 = FStar_Tactics_Types.goal_env g  in
                      let uu____3448 =
                        let uu____3449 =
                          let uu____3452 =
                            let uu____3453 =
                              let uu____3460 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3460)  in
                            FStar_Syntax_Syntax.NT uu____3453  in
                          [uu____3452]  in
                        FStar_Syntax_Subst.subst uu____3449 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3447
                        uu____3448 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3444
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3468  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3350
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3487 = cur_goal ()  in
      bind uu____3487
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3495 = FStar_Tactics_Types.goal_env goal  in
               let uu____3496 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3495 uu____3496
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3498 = __tc env t  in
           bind uu____3498
             (fun uu____3517  ->
                match uu____3517 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3532  ->
                         let uu____3533 =
                           let uu____3534 = FStar_Tactics_Types.goal_env goal
                              in
                           tts uu____3534 typ  in
                         let uu____3535 =
                           let uu____3536 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3536
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3533 uu____3535)
                      (fun uu____3539  ->
                         let uu____3540 =
                           let uu____3543 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3543 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3540
                           (fun uu____3545  ->
                              mlog
                                (fun uu____3549  ->
                                   let uu____3550 =
                                     let uu____3551 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     tts uu____3551 typ  in
                                   let uu____3552 =
                                     let uu____3553 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3554 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     tts uu____3553 uu____3554  in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3550 uu____3552)
                                (fun uu____3557  ->
                                   let uu____3558 =
                                     let uu____3561 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3562 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3561 typ uu____3562  in
                                   bind uu____3558
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3568 =
                                             let uu____3569 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3569 t1  in
                                           let uu____3570 =
                                             let uu____3571 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3571 typ  in
                                           let uu____3572 =
                                             let uu____3573 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3574 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3573 uu____3574  in
                                           let uu____3575 =
                                             let uu____3576 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3577 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3576 uu____3577  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3568 uu____3570 uu____3572
                                             uu____3575)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3592 =
        mlog
          (fun uu____3597  ->
             let uu____3598 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3598)
          (fun uu____3601  ->
             let uu____3602 =
               let uu____3609 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3609  in
             bind uu____3602
               (fun uu___88_3618  ->
                  match uu___88_3618 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3627 =
                        let uu____3634 =
                          let uu____3637 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3637
                            (fun uu____3642  ->
                               let uu____3643 = refine_intro ()  in
                               bind uu____3643
                                 (fun uu____3647  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3634  in
                      bind uu____3627
                        (fun uu___87_3654  ->
                           match uu___87_3654 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3662 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3592
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3691 =
             let uu____3694 =
               let uu____3697 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3697  in
             FStar_Util.set_elements uu____3694  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3691
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
          let uu____3775 = f x  in
          bind uu____3775
            (fun y  ->
               let uu____3783 = mapM f xs  in
               bind uu____3783 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3803 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3823 = cur_goal ()  in
        bind uu____3823
          (fun goal  ->
             mlog
               (fun uu____3830  ->
                  let uu____3831 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3831)
               (fun uu____3834  ->
                  let uu____3835 =
                    let uu____3840 =
                      let uu____3843 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3843  in
                    trytac_exn uu____3840  in
                  bind uu____3835
                    (fun uu___89_3850  ->
                       match uu___89_3850 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3858  ->
                                let uu____3859 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3859)
                             (fun uu____3862  ->
                                let uu____3863 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3863 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3887  ->
                                         let uu____3888 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3888)
                                      (fun uu____3891  ->
                                         let uu____3892 =
                                           let uu____3893 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3893  in
                                         if uu____3892
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3897 =
                                              let uu____3904 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3904
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3897
                                              (fun uu____3915  ->
                                                 match uu____3915 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____3942 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____3942
                                                        in
                                                     let uu____3945 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____3945
                                                       (fun uu____3953  ->
                                                          let u1 =
                                                            let uu____3955 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____3955
                                                              u
                                                             in
                                                          let uu____3956 =
                                                            let uu____3957 =
                                                              let uu____3960
                                                                =
                                                                let uu____3961
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____3961
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____3960
                                                               in
                                                            uu____3957.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____3956
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____3989)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4013
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4013
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    add_goals
                                                                    [(
                                                                    let uu___120_4018
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___120_4018.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___120_4018.FStar_Tactics_Types.opts);
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
      let uu____4073 =
        mlog
          (fun uu____4078  ->
             let uu____4079 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4079)
          (fun uu____4082  ->
             let uu____4083 = cur_goal ()  in
             bind uu____4083
               (fun goal  ->
                  let uu____4089 =
                    let uu____4098 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4098 tm  in
                  bind uu____4089
                    (fun uu____4112  ->
                       match uu____4112 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4125 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4125 typ  in
                           let uu____4126 =
                             let uu____4129 =
                               let uu____4132 = __apply uopt tm1 typ1  in
                               bind uu____4132
                                 (fun uu____4137  ->
                                    let uu____4138 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4138 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4129  in
                           let uu____4139 =
                             let uu____4142 =
                               let uu____4143 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4143 tm1  in
                             let uu____4144 =
                               let uu____4145 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4145 typ1  in
                             let uu____4146 =
                               let uu____4147 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4148 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4147 uu____4148  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4142 uu____4144 uu____4146
                              in
                           try_unif uu____4126 uu____4139)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4073
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4171 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4171
    then
      let uu____4178 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4197 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4238 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4178 with
      | (pre,post) ->
          let post1 =
            let uu____4274 =
              let uu____4283 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4283]  in
            FStar_Syntax_Util.mk_app post uu____4274  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4307 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4307
       then
         let uu____4314 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4314
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4347 =
      let uu____4350 =
        mlog
          (fun uu____4355  ->
             let uu____4356 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4356)
          (fun uu____4360  ->
             let is_unit_t t =
               let uu____4367 =
                 let uu____4368 = FStar_Syntax_Subst.compress t  in
                 uu____4368.FStar_Syntax_Syntax.n  in
               match uu____4367 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4372 -> false  in
             let uu____4373 = cur_goal ()  in
             bind uu____4373
               (fun goal  ->
                  let uu____4379 =
                    let uu____4388 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4388 tm  in
                  bind uu____4379
                    (fun uu____4403  ->
                       match uu____4403 with
                       | (tm1,t,guard) ->
                           let uu____4415 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4415 with
                            | (bs,comp) ->
                                let uu____4442 = lemma_or_sq comp  in
                                (match uu____4442 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4461 =
                                       FStar_List.fold_left
                                         (fun uu____4503  ->
                                            fun uu____4504  ->
                                              match (uu____4503, uu____4504)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4595 =
                                                    is_unit_t b_t  in
                                                  if uu____4595
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4631 =
                                                       let uu____4644 =
                                                         let uu____4645 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4645.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4648 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4644
                                                         uu____4648 b_t
                                                        in
                                                     match uu____4631 with
                                                     | (u,uu____4664,g_u) ->
                                                         let uu____4678 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4678,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4461 with
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
                                          let uu____4739 =
                                            let uu____4742 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4743 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4744 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4742 uu____4743
                                              uu____4744
                                             in
                                          bind uu____4739
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4752 =
                                                   let uu____4753 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4753 tm1  in
                                                 let uu____4754 =
                                                   let uu____4755 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4756 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4755 uu____4756
                                                    in
                                                 let uu____4757 =
                                                   let uu____4758 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4759 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4758 uu____4759
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4752 uu____4754
                                                   uu____4757
                                               else
                                                 (let uu____4761 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4761
                                                    (fun uu____4766  ->
                                                       let uu____4767 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4767
                                                         (fun uu____4775  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4800
                                                                  =
                                                                  let uu____4803
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4803
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4800
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
                                                                   let uu____4838
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4838)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4854
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4854
                                                              with
                                                              | (hd1,uu____4870)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4892)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4913
                                                                    -> false)
                                                               in
                                                            let uu____4914 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4979
                                                                     ->
                                                                    match uu____4979
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5002
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5002
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5028)
                                                                    ->
                                                                    let uu____5049
                                                                    =
                                                                    let uu____5050
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5050.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5049
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5064)
                                                                    ->
                                                                    let env =
                                                                    let uu___123_5086
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___123_5086.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let goal_ty
                                                                    =
                                                                    bnorm env
                                                                    ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let goal1
                                                                    =
                                                                    FStar_Tactics_Types.goal_with_type
                                                                    (let uu___124_5091
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___124_5091.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___124_5091.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___124_5091.FStar_Tactics_Types.is_guard)
                                                                    })
                                                                    goal_ty
                                                                     in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5104
                                                                    ->
                                                                    let env =
                                                                    let uu___125_5106
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___125_5106.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5108
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5108
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
                                                                    let uu____5111
                                                                    =
                                                                    let uu____5118
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5118
                                                                    term1  in
                                                                    match uu____5111
                                                                    with
                                                                    | 
                                                                    (uu____5119,uu____5120,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5122
                                                                    =
                                                                    let uu____5127
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5127
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5122
                                                                    (fun
                                                                    uu___90_5139
                                                                     ->
                                                                    match uu___90_5139
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
                                                            bind uu____4914
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5207
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5207
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5229
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5229
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5290
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5290
                                                                    then
                                                                    let uu____5293
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5293
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
                                                                    let uu____5307
                                                                    =
                                                                    let uu____5308
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5308
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5307)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5309
                                                                   =
                                                                   let uu____5312
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5312
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5309
                                                                   (fun
                                                                    uu____5315
                                                                     ->
                                                                    let uu____5316
                                                                    =
                                                                    let uu____5319
                                                                    =
                                                                    let uu____5320
                                                                    =
                                                                    let uu____5321
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5322
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5321
                                                                    uu____5322
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5320
                                                                     in
                                                                    if
                                                                    uu____5319
                                                                    then
                                                                    let uu____5325
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5325
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5316
                                                                    (fun
                                                                    uu____5329
                                                                     ->
                                                                    let uu____5330
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5330
                                                                    (fun
                                                                    uu____5334
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4350  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4347
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5356 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5356 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5366::(e1,uu____5368)::(e2,uu____5370)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5413 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5437 = destruct_eq' typ  in
    match uu____5437 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5467 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5467 with
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
        let uu____5529 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5529 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5577 = aux e'  in
               FStar_Util.map_opt uu____5577
                 (fun uu____5601  ->
                    match uu____5601 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5622 = aux e  in
      FStar_Util.map_opt uu____5622
        (fun uu____5646  ->
           match uu____5646 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5713 =
            let uu____5722 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5722  in
          FStar_Util.map_opt uu____5713
            (fun uu____5737  ->
               match uu____5737 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___126_5756 = bv  in
                     let uu____5757 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___126_5756.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___126_5756.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5757
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___127_5765 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5766 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5773 =
                       let uu____5776 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5776  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___127_5765.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5766;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5773;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___127_5765.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___127_5765.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___127_5765.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___128_5777 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___128_5777.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___128_5777.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___128_5777.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5787 = cur_goal ()  in
    bind uu____5787
      (fun goal  ->
         let uu____5795 = h  in
         match uu____5795 with
         | (bv,uu____5799) ->
             mlog
               (fun uu____5803  ->
                  let uu____5804 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5805 =
                    let uu____5806 = FStar_Tactics_Types.goal_env goal  in
                    tts uu____5806 bv.FStar_Syntax_Syntax.sort  in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5804
                    uu____5805)
               (fun uu____5809  ->
                  let uu____5810 =
                    let uu____5819 = FStar_Tactics_Types.goal_env goal  in
                    split_env bv uu____5819  in
                  match uu____5810 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5840 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5840 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5855 =
                             let uu____5856 = FStar_Syntax_Subst.compress x
                                in
                             uu____5856.FStar_Syntax_Syntax.n  in
                           (match uu____5855 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___129_5873 = bv1  in
                                  let uu____5874 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___129_5873.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___129_5873.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5874
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let new_env = push_bvs e0 (bv :: bvs1)  in
                                let new_goal =
                                  let uu___130_5882 =
                                    goal.FStar_Tactics_Types.goal_ctx_uvar
                                     in
                                  let uu____5883 =
                                    FStar_TypeChecker_Env.all_binders new_env
                                     in
                                  let uu____5890 =
                                    let uu____5893 =
                                      FStar_Tactics_Types.goal_type goal  in
                                    FStar_Syntax_Subst.subst s uu____5893  in
                                  {
                                    FStar_Syntax_Syntax.ctx_uvar_head =
                                      (uu___130_5882.FStar_Syntax_Syntax.ctx_uvar_head);
                                    FStar_Syntax_Syntax.ctx_uvar_gamma =
                                      (new_env.FStar_TypeChecker_Env.gamma);
                                    FStar_Syntax_Syntax.ctx_uvar_binders =
                                      uu____5883;
                                    FStar_Syntax_Syntax.ctx_uvar_typ =
                                      uu____5890;
                                    FStar_Syntax_Syntax.ctx_uvar_reason =
                                      (uu___130_5882.FStar_Syntax_Syntax.ctx_uvar_reason);
                                    FStar_Syntax_Syntax.ctx_uvar_should_check
                                      =
                                      (uu___130_5882.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                    FStar_Syntax_Syntax.ctx_uvar_range =
                                      (uu___130_5882.FStar_Syntax_Syntax.ctx_uvar_range)
                                  }  in
                                replace_cur
                                  (let uu___131_5896 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___131_5896.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       new_goal;
                                     FStar_Tactics_Types.opts =
                                       (uu___131_5896.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___131_5896.FStar_Tactics_Types.is_guard)
                                   })
                            | uu____5897 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5898 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5919 = cur_goal ()  in
      bind uu____5919
        (fun goal  ->
           let uu____5930 = b  in
           match uu____5930 with
           | (bv,uu____5934) ->
               let bv' =
                 let uu____5936 =
                   let uu___132_5937 = bv  in
                   let uu____5938 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5938;
                     FStar_Syntax_Syntax.index =
                       (uu___132_5937.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___132_5937.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5936  in
               let s1 =
                 let uu____5942 =
                   let uu____5943 =
                     let uu____5950 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5950)  in
                   FStar_Syntax_Syntax.NT uu____5943  in
                 [uu____5942]  in
               let uu____5955 = subst_goal bv bv' s1 goal  in
               (match uu____5955 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5970 = cur_goal ()  in
    bind uu____5970
      (fun goal  ->
         let uu____5979 = b  in
         match uu____5979 with
         | (bv,uu____5983) ->
             let uu____5984 =
               let uu____5993 = FStar_Tactics_Types.goal_env goal  in
               split_env bv uu____5993  in
             (match uu____5984 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____6014 = FStar_Syntax_Util.type_u ()  in
                  (match uu____6014 with
                   | (ty,u) ->
                       let uu____6023 = new_uvar "binder_retype" e0 ty  in
                       bind uu____6023
                         (fun uu____6041  ->
                            match uu____6041 with
                            | (t',u_t') ->
                                let bv'' =
                                  let uu___133_6051 = bv  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___133_6051.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___133_6051.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t'
                                  }  in
                                let s =
                                  let uu____6055 =
                                    let uu____6056 =
                                      let uu____6063 =
                                        FStar_Syntax_Syntax.bv_to_name bv''
                                         in
                                      (bv, uu____6063)  in
                                    FStar_Syntax_Syntax.NT uu____6056  in
                                  [uu____6055]  in
                                let bvs1 =
                                  FStar_List.map
                                    (fun b1  ->
                                       let uu___134_6075 = b1  in
                                       let uu____6076 =
                                         FStar_Syntax_Subst.subst s
                                           b1.FStar_Syntax_Syntax.sort
                                          in
                                       {
                                         FStar_Syntax_Syntax.ppname =
                                           (uu___134_6075.FStar_Syntax_Syntax.ppname);
                                         FStar_Syntax_Syntax.index =
                                           (uu___134_6075.FStar_Syntax_Syntax.index);
                                         FStar_Syntax_Syntax.sort =
                                           uu____6076
                                       }) bvs
                                   in
                                let env' = push_bvs e0 (bv'' :: bvs1)  in
                                bind __dismiss
                                  (fun uu____6083  ->
                                     let new_goal =
                                       let uu____6085 =
                                         FStar_Tactics_Types.goal_with_env
                                           goal env'
                                          in
                                       let uu____6086 =
                                         let uu____6087 =
                                           FStar_Tactics_Types.goal_type goal
                                            in
                                         FStar_Syntax_Subst.subst s
                                           uu____6087
                                          in
                                       FStar_Tactics_Types.goal_with_type
                                         uu____6085 uu____6086
                                        in
                                     let uu____6088 = add_goals [new_goal]
                                        in
                                     bind uu____6088
                                       (fun uu____6093  ->
                                          let uu____6094 =
                                            FStar_Syntax_Util.mk_eq2
                                              (FStar_Syntax_Syntax.U_succ u)
                                              ty bv.FStar_Syntax_Syntax.sort
                                              t'
                                             in
                                          add_irrelevant_goal
                                            "binder_retype equation" e0
                                            uu____6094
                                            goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6113 = cur_goal ()  in
      bind uu____6113
        (fun goal  ->
           let uu____6122 = b  in
           match uu____6122 with
           | (bv,uu____6126) ->
               let uu____6127 =
                 let uu____6136 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6136  in
               (match uu____6127 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____6160 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____6160
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___135_6165 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___135_6165.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___135_6165.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    let uu____6167 =
                      FStar_Tactics_Types.goal_with_env goal env'  in
                    replace_cur uu____6167))
  
let (revert : unit -> unit tac) =
  fun uu____6174  ->
    let uu____6177 = cur_goal ()  in
    bind uu____6177
      (fun goal  ->
         let uu____6183 =
           let uu____6190 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6190  in
         match uu____6183 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6206 =
                 let uu____6209 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6209  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6206
                in
             let uu____6218 = new_uvar "revert" env' typ'  in
             bind uu____6218
               (fun uu____6233  ->
                  match uu____6233 with
                  | (r,u_r) ->
                      let uu____6242 =
                        let uu____6245 =
                          let uu____6246 =
                            let uu____6247 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6247.FStar_Syntax_Syntax.pos  in
                          let uu____6250 =
                            let uu____6255 =
                              let uu____6256 =
                                let uu____6263 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6263  in
                              [uu____6256]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6255  in
                          uu____6250 FStar_Pervasives_Native.None uu____6246
                           in
                        set_solution goal uu____6245  in
                      bind uu____6242
                        (fun uu____6280  ->
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
      let uu____6292 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6292
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6305 = cur_goal ()  in
    bind uu____6305
      (fun goal  ->
         mlog
           (fun uu____6313  ->
              let uu____6314 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6315 =
                let uu____6316 =
                  let uu____6317 =
                    let uu____6324 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6324  in
                  FStar_All.pipe_right uu____6317 FStar_List.length  in
                FStar_All.pipe_right uu____6316 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6314 uu____6315)
           (fun uu____6337  ->
              let uu____6338 =
                let uu____6347 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6347  in
              match uu____6338 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6386 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6386
                        then
                          let uu____6389 =
                            let uu____6390 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6390
                             in
                          fail uu____6389
                        else check1 bvs2
                     in
                  let uu____6392 =
                    let uu____6393 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6393  in
                  if uu____6392
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6397 = check1 bvs  in
                     bind uu____6397
                       (fun uu____6403  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6405 =
                            let uu____6412 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6412  in
                          bind uu____6405
                            (fun uu____6421  ->
                               match uu____6421 with
                               | (ut,uvar_ut) ->
                                   let uu____6430 = set_solution goal ut  in
                                   bind uu____6430
                                     (fun uu____6435  ->
                                        let uu____6436 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6436))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6443  ->
    let uu____6446 = cur_goal ()  in
    bind uu____6446
      (fun goal  ->
         let uu____6452 =
           let uu____6459 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6459  in
         match uu____6452 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6467) ->
             let uu____6472 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6472)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6482 = cur_goal ()  in
    bind uu____6482
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6492 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6492  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6495  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6505 = cur_goal ()  in
    bind uu____6505
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6515 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6515  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6518  -> add_goals [g']))
  
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
            let uu____6558 = FStar_Syntax_Subst.compress t  in
            uu____6558.FStar_Syntax_Syntax.n  in
          let uu____6561 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___139_6567 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___139_6567.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___139_6567.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6561
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6583 =
                   let uu____6584 = FStar_Syntax_Subst.compress t1  in
                   uu____6584.FStar_Syntax_Syntax.n  in
                 match uu____6583 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6611 = ff hd1  in
                     bind uu____6611
                       (fun hd2  ->
                          let fa uu____6633 =
                            match uu____6633 with
                            | (a,q) ->
                                let uu____6646 = ff a  in
                                bind uu____6646 (fun a1  -> ret (a1, q))
                             in
                          let uu____6659 = mapM fa args  in
                          bind uu____6659
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6725 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6725 with
                      | (bs1,t') ->
                          let uu____6734 =
                            let uu____6737 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6737 t'  in
                          bind uu____6734
                            (fun t''  ->
                               let uu____6741 =
                                 let uu____6742 =
                                   let uu____6759 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6766 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6759, uu____6766, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6742  in
                               ret uu____6741))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6835 = ff hd1  in
                     bind uu____6835
                       (fun hd2  ->
                          let ffb br =
                            let uu____6850 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6850 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6882 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6882  in
                                let uu____6883 = ff1 e  in
                                bind uu____6883
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6898 = mapM ffb brs  in
                          bind uu____6898
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6942;
                          FStar_Syntax_Syntax.lbtyp = uu____6943;
                          FStar_Syntax_Syntax.lbeff = uu____6944;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6946;
                          FStar_Syntax_Syntax.lbpos = uu____6947;_}::[]),e)
                     ->
                     let lb =
                       let uu____6972 =
                         let uu____6973 = FStar_Syntax_Subst.compress t1  in
                         uu____6973.FStar_Syntax_Syntax.n  in
                       match uu____6972 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6977) -> lb
                       | uu____6990 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6999 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6999
                         (fun def1  ->
                            ret
                              (let uu___136_7005 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___136_7005.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___136_7005.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___136_7005.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___136_7005.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___136_7005.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___136_7005.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7006 = fflb lb  in
                     bind uu____7006
                       (fun lb1  ->
                          let uu____7016 =
                            let uu____7021 =
                              let uu____7022 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7022]  in
                            FStar_Syntax_Subst.open_term uu____7021 e  in
                          match uu____7016 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7046 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7046  in
                              let uu____7047 = ff1 e1  in
                              bind uu____7047
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7088 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7088
                         (fun def  ->
                            ret
                              (let uu___137_7094 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___137_7094.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___137_7094.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___137_7094.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___137_7094.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___137_7094.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___137_7094.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7095 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7095 with
                      | (lbs1,e1) ->
                          let uu____7110 = mapM fflb lbs1  in
                          bind uu____7110
                            (fun lbs2  ->
                               let uu____7122 = ff e1  in
                               bind uu____7122
                                 (fun e2  ->
                                    let uu____7130 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7130 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7198 = ff t2  in
                     bind uu____7198
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7229 = ff t2  in
                     bind uu____7229
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7236 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___138_7243 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___138_7243.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___138_7243.FStar_Syntax_Syntax.vars)
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
            let uu____7280 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7280 with
            | (t1,lcomp,g) ->
                let uu____7292 =
                  (let uu____7295 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7295) ||
                    (let uu____7297 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7297)
                   in
                if uu____7292
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7307 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7307
                       (fun uu____7323  ->
                          match uu____7323 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7336  ->
                                    let uu____7337 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7338 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7337 uu____7338);
                               (let uu____7339 =
                                  let uu____7342 =
                                    let uu____7343 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7343 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7342
                                    opts
                                   in
                                bind uu____7339
                                  (fun uu____7346  ->
                                     let uu____7347 =
                                       bind tau
                                         (fun uu____7353  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7359  ->
                                                 let uu____7360 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7361 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7360 uu____7361);
                                            ret ut1)
                                        in
                                     focus uu____7347))))
                      in
                   let uu____7362 = trytac' rewrite_eq  in
                   bind uu____7362
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
          let uu____7560 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7560
            (fun t1  ->
               let uu____7568 =
                 f env
                   (let uu___142_7577 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___142_7577.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___142_7577.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7568
                 (fun uu____7593  ->
                    match uu____7593 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7616 =
                               let uu____7617 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7617.FStar_Syntax_Syntax.n  in
                             match uu____7616 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7650 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7650
                                   (fun uu____7675  ->
                                      match uu____7675 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7691 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7691
                                            (fun uu____7718  ->
                                               match uu____7718 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___140_7748 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___140_7748.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___140_7748.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7784 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7784 with
                                  | (bs1,t') ->
                                      let uu____7799 =
                                        let uu____7806 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7806 ctrl1 t'
                                         in
                                      bind uu____7799
                                        (fun uu____7824  ->
                                           match uu____7824 with
                                           | (t'',ctrl2) ->
                                               let uu____7839 =
                                                 let uu____7846 =
                                                   let uu___141_7849 = t4  in
                                                   let uu____7852 =
                                                     let uu____7853 =
                                                       let uu____7870 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7877 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7870,
                                                         uu____7877, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7853
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7852;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___141_7849.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___141_7849.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7846, ctrl2)  in
                                               ret uu____7839))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7924 -> ret (t3, ctrl1))))

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
              let uu____7967 = ctrl_tac_fold f env ctrl t  in
              bind uu____7967
                (fun uu____7991  ->
                   match uu____7991 with
                   | (t1,ctrl1) ->
                       let uu____8006 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8006
                         (fun uu____8033  ->
                            match uu____8033 with
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
              let uu____8115 =
                let uu____8122 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8122
                  (fun uu____8131  ->
                     let uu____8132 = ctrl t1  in
                     bind uu____8132
                       (fun res  ->
                          let uu____8155 = trivial ()  in
                          bind uu____8155 (fun uu____8163  -> ret res)))
                 in
              bind uu____8115
                (fun uu____8179  ->
                   match uu____8179 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8203 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8203 with
                          | (t2,lcomp,g) ->
                              let uu____8219 =
                                (let uu____8222 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8222) ||
                                  (let uu____8224 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8224)
                                 in
                              if uu____8219
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8239 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8239
                                   (fun uu____8259  ->
                                      match uu____8259 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8276  ->
                                                let uu____8277 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8278 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8277 uu____8278);
                                           (let uu____8279 =
                                              let uu____8282 =
                                                let uu____8283 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8283 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8282 opts
                                               in
                                            bind uu____8279
                                              (fun uu____8290  ->
                                                 let uu____8291 =
                                                   bind rewriter
                                                     (fun uu____8305  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8311  ->
                                                             let uu____8312 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8313 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8312
                                                               uu____8313);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8291)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____8361 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8361 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8398  ->
                     let uu____8399 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____8399);
                bind dismiss_all
                  (fun uu____8402  ->
                     let uu____8403 =
                       let uu____8410 = FStar_Tactics_Types.goal_env g  in
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts) uu____8410 keepGoing
                         gt1
                        in
                     bind uu____8403
                       (fun uu____8422  ->
                          match uu____8422 with
                          | (gt',uu____8430) ->
                              (log ps
                                 (fun uu____8434  ->
                                    let uu____8435 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____8435);
                               (let uu____8436 = push_goals gs  in
                                bind uu____8436
                                  (fun uu____8441  ->
                                     let uu____8442 =
                                       let uu____8445 =
                                         FStar_Tactics_Types.goal_with_type g
                                           gt'
                                          in
                                       [uu____8445]  in
                                     add_goals uu____8442)))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____8471 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8471 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8508  ->
                     let uu____8509 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____8509);
                bind dismiss_all
                  (fun uu____8512  ->
                     let uu____8513 =
                       let uu____8516 = FStar_Tactics_Types.goal_env g  in
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         uu____8516 gt1
                        in
                     bind uu____8513
                       (fun gt'  ->
                          log ps
                            (fun uu____8524  ->
                               let uu____8525 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____8525);
                          (let uu____8526 = push_goals gs  in
                           bind uu____8526
                             (fun uu____8531  ->
                                let uu____8532 =
                                  let uu____8535 =
                                    FStar_Tactics_Types.goal_with_type g gt'
                                     in
                                  [uu____8535]  in
                                add_goals uu____8532))))))
  
let (trefl : unit -> unit tac) =
  fun uu____8542  ->
    let uu____8545 = cur_goal ()  in
    bind uu____8545
      (fun g  ->
         let uu____8563 =
           let uu____8568 = FStar_Tactics_Types.goal_type g  in
           FStar_Syntax_Util.un_squash uu____8568  in
         match uu____8563 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8576 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8576 with
              | (hd1,args) ->
                  let uu____8609 =
                    let uu____8620 =
                      let uu____8621 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8621.FStar_Syntax_Syntax.n  in
                    (uu____8620, args)  in
                  (match uu____8609 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8633::(l,uu____8635)::(r,uu____8637)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8664 =
                         let uu____8667 = FStar_Tactics_Types.goal_env g  in
                         do_unify uu____8667 l r  in
                       bind uu____8664
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8674 =
                                let uu____8675 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8675 l  in
                              let uu____8676 =
                                let uu____8677 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8677 r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8674 uu____8676
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8680) ->
                       let uu____8693 =
                         let uu____8694 = FStar_Tactics_Types.goal_env g  in
                         tts uu____8694 t  in
                       fail1 "trefl: not an equality (%s)" uu____8693))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8703  ->
    let uu____8706 = cur_goal ()  in
    bind uu____8706
      (fun g  ->
         let uu____8712 =
           let uu____8719 = FStar_Tactics_Types.goal_env g  in
           let uu____8720 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8719 uu____8720  in
         bind uu____8712
           (fun uu____8729  ->
              match uu____8729 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___143_8739 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___143_8739.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___143_8739.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___143_8739.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8742  ->
                       let uu____8743 =
                         let uu____8746 = FStar_Tactics_Types.goal_env g  in
                         let uu____8747 =
                           let uu____8748 =
                             let uu____8749 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8750 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8749
                               uu____8750
                              in
                           let uu____8751 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8752 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8748 uu____8751 u
                             uu____8752
                            in
                         add_irrelevant_goal "dup equation" uu____8746
                           uu____8747 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8743
                         (fun uu____8755  ->
                            let uu____8756 = add_goals [g']  in
                            bind uu____8756 (fun uu____8760  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8767  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___144_8784 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___144_8784.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___144_8784.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___144_8784.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___144_8784.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___144_8784.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___144_8784.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___144_8784.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___144_8784.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___144_8784.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___144_8784.FStar_Tactics_Types.freshness)
                })
         | uu____8785 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8794  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___145_8807 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___145_8807.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___145_8807.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___145_8807.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___145_8807.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___145_8807.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___145_8807.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___145_8807.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___145_8807.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___145_8807.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___145_8807.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8814  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8821 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8841 =
      let uu____8848 = cur_goal ()  in
      bind uu____8848
        (fun g  ->
           let uu____8858 =
             let uu____8867 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8867 t  in
           bind uu____8858
             (fun uu____8895  ->
                match uu____8895 with
                | (t1,typ,guard) ->
                    let uu____8911 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8911 with
                     | (hd1,args) ->
                         let uu____8954 =
                           let uu____8967 =
                             let uu____8968 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8968.FStar_Syntax_Syntax.n  in
                           (uu____8967, args)  in
                         (match uu____8954 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8987)::(q,uu____8989)::[]) when
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
                                let uu____9027 =
                                  let uu____9028 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9028
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9027
                                 in
                              let g2 =
                                let uu____9030 =
                                  let uu____9031 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9031
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9030
                                 in
                              bind __dismiss
                                (fun uu____9038  ->
                                   let uu____9039 = add_goals [g1; g2]  in
                                   bind uu____9039
                                     (fun uu____9048  ->
                                        let uu____9049 =
                                          let uu____9054 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9055 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9054, uu____9055)  in
                                        ret uu____9049))
                          | uu____9060 ->
                              let uu____9073 =
                                let uu____9074 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9074 typ  in
                              fail1 "Not a disjunction: %s" uu____9073))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8841
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9104 = cur_goal ()  in
    bind uu____9104
      (fun g  ->
         FStar_Options.push ();
         (let uu____9117 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____9117);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___146_9124 = g  in
                 {
                   FStar_Tactics_Types.goal_main_env =
                     (uu___146_9124.FStar_Tactics_Types.goal_main_env);
                   FStar_Tactics_Types.goal_ctx_uvar =
                     (uu___146_9124.FStar_Tactics_Types.goal_ctx_uvar);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___146_9124.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____9132  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9145  ->
    let uu____9148 = cur_goal ()  in
    bind uu____9148
      (fun g  ->
         let uu____9154 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9154)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9163  ->
    let uu____9166 = cur_goal ()  in
    bind uu____9166
      (fun g  ->
         let uu____9172 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9172)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9181  ->
    let uu____9184 = cur_goal ()  in
    bind uu____9184
      (fun g  ->
         let uu____9190 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9190)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9207 =
        let uu____9210 = cur_goal ()  in
        bind uu____9210
          (fun goal  ->
             let env =
               let uu____9218 = FStar_Tactics_Types.goal_env goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____9218 ty  in
             let uu____9219 = __tc env tm  in
             bind uu____9219
               (fun uu____9239  ->
                  match uu____9239 with
                  | (tm1,typ,guard) ->
                      let uu____9251 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____9251 (fun uu____9255  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9207
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9278 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9284 =
              let uu____9291 =
                let uu____9292 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9292
                 in
              new_uvar "uvar_env.2" env uu____9291  in
            bind uu____9284
              (fun uu____9308  ->
                 match uu____9308 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9278
        (fun typ  ->
           let uu____9320 = new_uvar "uvar_env" env typ  in
           bind uu____9320
             (fun uu____9334  -> match uu____9334 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9352 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9371 -> g.FStar_Tactics_Types.opts
             | uu____9374 -> FStar_Options.peek ()  in
           let uu____9377 = FStar_Syntax_Util.head_and_args t  in
           match uu____9377 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9395);
                FStar_Syntax_Syntax.pos = uu____9396;
                FStar_Syntax_Syntax.vars = uu____9397;_},uu____9398)
               ->
               let env1 =
                 let uu___147_9440 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___147_9440.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___147_9440.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___147_9440.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___147_9440.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___147_9440.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___147_9440.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___147_9440.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___147_9440.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___147_9440.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___147_9440.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___147_9440.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___147_9440.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___147_9440.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___147_9440.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___147_9440.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___147_9440.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___147_9440.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___147_9440.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___147_9440.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___147_9440.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___147_9440.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___147_9440.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___147_9440.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___147_9440.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___147_9440.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___147_9440.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___147_9440.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___147_9440.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___147_9440.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___147_9440.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___147_9440.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___147_9440.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___147_9440.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___147_9440.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___147_9440.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___147_9440.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___147_9440.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let g1 =
                 let uu____9443 =
                   bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
                 FStar_Tactics_Types.goal_with_type g uu____9443  in
               add_goals [g1]
           | uu____9444 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9352
  
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
          (fun uu____9505  ->
             let uu____9506 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9506
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
        (fun uu____9527  ->
           let uu____9528 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9528)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9538 =
      mlog
        (fun uu____9543  ->
           let uu____9544 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9544)
        (fun uu____9547  ->
           let uu____9548 = cur_goal ()  in
           bind uu____9548
             (fun g  ->
                let uu____9554 =
                  let uu____9563 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9563 ty  in
                bind uu____9554
                  (fun uu____9575  ->
                     match uu____9575 with
                     | (ty1,uu____9585,guard) ->
                         let uu____9587 =
                           let uu____9590 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9590 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9587
                           (fun uu____9593  ->
                              let uu____9594 =
                                let uu____9597 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9598 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9597 uu____9598 ty1  in
                              bind uu____9594
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9604 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9604
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
                                        let uu____9610 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9611 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9610 uu____9611
                                         in
                                      let nty =
                                        let uu____9613 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9613 ty1  in
                                      let uu____9614 =
                                        let uu____9617 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9617 ng nty  in
                                      bind uu____9614
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9623 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9623
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9538
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9645::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9673 = init xs  in x :: uu____9673
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9690) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9747 = last args  in
        (match uu____9747 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9769 =
               let uu____9770 =
                 let uu____9775 =
                   let uu____9776 =
                     let uu____9781 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9781  in
                   uu____9776 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9775, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9770  in
             FStar_All.pipe_left ret uu____9769)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9792,uu____9793) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9837 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9837 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9870 =
                    let uu____9871 =
                      let uu____9876 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9876)  in
                    FStar_Reflection_Data.Tv_Abs uu____9871  in
                  FStar_All.pipe_left ret uu____9870))
    | FStar_Syntax_Syntax.Tm_type uu____9879 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9899 ->
        let uu____9912 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9912 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9942 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9942 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9981 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9989 =
          let uu____9990 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____9990  in
        FStar_All.pipe_left ret uu____9989
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
        let uu____10015 =
          let uu____10016 =
            let uu____10021 =
              let uu____10022 =
                FStar_Syntax_Unionfind.uvar_id
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_BigInt.of_int_fs uu____10022  in
            (uu____10021, (ctx_u, s))  in
          FStar_Reflection_Data.Tv_Uvar uu____10016  in
        FStar_All.pipe_left ret uu____10015
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____10058 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____10063 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____10063 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____10102 ->
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
           | FStar_Util.Inr uu____10132 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____10136 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____10136 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____10156 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____10160 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____10214 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____10214
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____10233 =
                let uu____10240 =
                  FStar_List.map
                    (fun uu____10252  ->
                       match uu____10252 with
                       | (p1,uu____10260) -> inspect_pat p1) ps
                   in
                (fv, uu____10240)  in
              FStar_Reflection_Data.Pat_Cons uu____10233
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
            (fun uu___91_10344  ->
               match uu___91_10344 with
               | (pat,uu____10362,t4) ->
                   let uu____10376 = inspect_pat pat  in (uu____10376, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____10383 ->
        ((let uu____10385 =
            let uu____10390 =
              let uu____10391 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____10392 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____10391
                uu____10392
               in
            (FStar_Errors.Warning_CantInspect, uu____10390)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10385);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10405 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10405
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10409 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10409
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10413 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10413
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10420 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10420
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10443 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10443
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10460 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10460
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10479 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10479
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10487 =
          let uu____10490 =
            let uu____10497 =
              let uu____10498 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10498  in
            FStar_Syntax_Syntax.mk uu____10497  in
          uu____10490 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10487
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10508 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10508
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10521 =
          let uu____10524 =
            let uu____10531 =
              let uu____10532 =
                let uu____10545 =
                  let uu____10548 =
                    let uu____10549 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10549]  in
                  FStar_Syntax_Subst.close uu____10548 t2  in
                ((false, [lb]), uu____10545)  in
              FStar_Syntax_Syntax.Tm_let uu____10532  in
            FStar_Syntax_Syntax.mk uu____10531  in
          uu____10524 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10521
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10585 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10585 with
         | (lbs,body) ->
             let uu____10600 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10600)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10638 =
                let uu____10639 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10639  in
              FStar_All.pipe_left wrap uu____10638
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10646 =
                let uu____10647 =
                  let uu____10660 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10676 = pack_pat p1  in
                         (uu____10676, false)) ps
                     in
                  (fv, uu____10660)  in
                FStar_Syntax_Syntax.Pat_cons uu____10647  in
              FStar_All.pipe_left wrap uu____10646
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
            (fun uu___92_10722  ->
               match uu___92_10722 with
               | (pat,t1) ->
                   let uu____10739 = pack_pat pat  in
                   (uu____10739, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10787 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10787
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10819 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10819
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10869 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10869
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10912 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10912
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10933 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10933 with
      | (u,ctx_uvars,g_u) ->
          let uu____10965 = FStar_List.hd ctx_uvars  in
          (match uu____10965 with
           | (ctx_uvar,uu____10979) ->
               let g =
                 let uu____10981 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____10981 false
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
      let uu____10996 = goal_of_goal_ty env typ  in
      match uu____10996 with
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
          let uu____11012 = FStar_Tactics_Types.goal_witness g  in
          (ps, uu____11012)
  