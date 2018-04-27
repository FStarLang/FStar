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
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let g_binders =
      let uu____205 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      FStar_All.pipe_right uu____205
        (FStar_Syntax_Print.binders_to_string ", ")
       in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness
       in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
       in
    let uu____208 = tts g.FStar_Tactics_Types.context w  in
    let uu____209 = tts g.FStar_Tactics_Types.context t  in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____208 uu____209
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____225 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____225
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____241 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____241
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____262 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____262
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____269) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____279) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____294 =
      let uu____297 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty
         in
      FStar_Syntax_Util.un_squash uu____297  in
    match uu____294 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____299 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____325 =
            let uu____326 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____326  in
          if uu____325 then tacprint msg else ());
         ret ())
  
let dump_goal : 'Auu____334 . 'Auu____334 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  -> let uu____346 = goal_to_string goal  in tacprint uu____346
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____358 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____362 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____362))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____371  ->
    match uu____371 with
    | (msg,ps) ->
        let uu____378 =
          let uu____381 =
            let uu____382 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____382 msg
             in
          let uu____383 =
            let uu____386 =
              let uu____387 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____387  in
            let uu____388 =
              let uu____391 =
                let uu____392 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____393 =
                  let uu____394 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____394  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____392
                  uu____393
                 in
              let uu____397 =
                let uu____400 =
                  let uu____401 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____402 =
                    let uu____403 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____403  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____401
                    uu____402
                   in
                [uu____400]  in
              uu____391 :: uu____397  in
            uu____386 :: uu____388  in
          uu____381 :: uu____383  in
        FStar_String.concat "" uu____378
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____412 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      let uu____413 =
        let uu____418 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____418  in
      FStar_All.pipe_right uu____412 uu____413  in
    let uu____419 =
      let uu____426 =
        let uu____433 =
          let uu____438 =
            let uu____439 =
              let uu____446 =
                let uu____451 =
                  let uu____452 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____452  in
                ("witness", uu____451)  in
              let uu____453 =
                let uu____460 =
                  let uu____465 =
                    let uu____466 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____466  in
                  ("type", uu____465)  in
                [uu____460]  in
              uu____446 :: uu____453  in
            FStar_Util.JsonAssoc uu____439  in
          ("goal", uu____438)  in
        [uu____433]  in
      ("hyps", g_binders) :: uu____426  in
    FStar_Util.JsonAssoc uu____419
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____499  ->
    match uu____499 with
    | (msg,ps) ->
        let uu____506 =
          let uu____513 =
            let uu____520 =
              let uu____527 =
                let uu____534 =
                  let uu____539 =
                    let uu____540 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____540  in
                  ("goals", uu____539)  in
                let uu____543 =
                  let uu____550 =
                    let uu____555 =
                      let uu____556 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____556  in
                    ("smt-goals", uu____555)  in
                  [uu____550]  in
                uu____534 :: uu____543  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____527
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____520  in
          let uu____579 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____592 =
                let uu____597 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____597)  in
              [uu____592]
            else []  in
          FStar_List.append uu____513 uu____579  in
        FStar_Util.JsonAssoc uu____506
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____627  ->
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
         (let uu____650 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____650 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____668 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____668 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____701 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____701 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____732 =
              let uu____735 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____735  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____732);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____816 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____816
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____824 . Prims.string -> Prims.string -> 'Auu____824 tac =
  fun msg  ->
    fun x  -> let uu____837 = FStar_Util.format1 msg x  in fail uu____837
  
let fail2 :
  'Auu____846 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____846 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____864 = FStar_Util.format2 msg x y  in fail uu____864
  
let fail3 :
  'Auu____875 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____875 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____898 = FStar_Util.format3 msg x y z  in fail uu____898
  
let fail4 :
  'Auu____911 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____911 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____939 = FStar_Util.format4 msg x y z w  in fail uu____939
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____972 = run t ps  in
         match uu____972 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___67_996 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___67_996.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___67_996.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___67_996.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___67_996.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___67_996.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___67_996.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___67_996.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___67_996.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___67_996.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___67_996.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1023 = trytac' t  in
    bind uu____1023
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1050 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1086 = trytac t  in run uu____1086 ps
         with
         | FStar_Errors.Err (uu____1102,msg) ->
             (log ps
                (fun uu____1106  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1111,msg,uu____1113) ->
             (log ps
                (fun uu____1116  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1149 = run t ps  in
           match uu____1149 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1168  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1189 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1189
         then
           let uu____1190 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1191 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1190
             uu____1191
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1203 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1203
            then
              let uu____1204 = FStar_Util.string_of_bool res  in
              let uu____1205 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1206 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1204 uu____1205 uu____1206
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1214,msg) ->
             mlog
               (fun uu____1217  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1219  -> ret false)
         | FStar_Errors.Error (uu____1220,msg,r) ->
             mlog
               (fun uu____1225  ->
                  let uu____1226 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1226) (fun uu____1228  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1251  ->
             (let uu____1253 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1253
              then
                (FStar_Options.push ();
                 (let uu____1255 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1257 =
                let uu____1260 = __do_unify env t1 t2  in
                bind uu____1260
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
              bind uu____1257
                (fun r  ->
                   (let uu____1276 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1276 then FStar_Options.pop () else ());
                   ret r)))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1297 =
         let uu___72_1298 = p  in
         let uu____1299 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___72_1298.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___72_1298.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___72_1298.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1299;
           FStar_Tactics_Types.smt_goals =
             (uu___72_1298.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___72_1298.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___72_1298.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___72_1298.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___72_1298.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___72_1298.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___72_1298.FStar_Tactics_Types.freshness)
         }  in
       set uu____1297)
  
let (dismiss : unit -> unit tac) =
  fun uu____1308  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1315 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1332 = trysolve goal solution  in
      bind uu____1332
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1340 =
                let uu____1341 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1342 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1343 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1341
                  uu____1342 uu____1343
                 in
              fail uu____1340))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___73_1350 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___73_1350.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___73_1350.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___73_1350.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___73_1350.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___73_1350.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___73_1350.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___73_1350.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___73_1350.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___73_1350.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___73_1350.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1369 = FStar_Options.defensive ()  in
    if uu____1369
    then
      let b = true  in
      let env = g.FStar_Tactics_Types.context  in
      let b1 =
        b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness)
         in
      let b2 =
        b1 &&
          (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty)
         in
      let rec aux b3 e =
        let uu____1385 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1385 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1403 =
        (let uu____1406 = aux b2 env  in Prims.op_Negation uu____1406) &&
          (let uu____1408 = FStar_ST.op_Bang nwarn  in
           uu____1408 < (Prims.parse_int "5"))
         in
      (if uu____1403
       then
         ((let uu____1433 =
             let uu____1438 =
               let uu____1439 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1439
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1438)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1433);
          (let uu____1440 =
             let uu____1441 = FStar_ST.op_Bang nwarn  in
             uu____1441 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1440))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___74_1509 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___74_1509.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___74_1509.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___74_1509.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___74_1509.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___74_1509.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___74_1509.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___74_1509.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___74_1509.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___74_1509.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___74_1509.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___75_1529 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___75_1529.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___75_1529.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___75_1529.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___75_1529.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___75_1529.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___75_1529.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___75_1529.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___75_1529.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___75_1529.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___75_1529.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___76_1549 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___76_1549.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___76_1549.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___76_1549.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___76_1549.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___76_1549.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___76_1549.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___76_1549.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___76_1549.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___76_1549.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___76_1549.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___77_1569 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___77_1569.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___77_1569.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___77_1569.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___77_1569.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___77_1569.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___77_1569.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___77_1569.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___77_1569.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___77_1569.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___77_1569.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1580  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___78_1594 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___78_1594.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___78_1594.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___78_1594.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___78_1594.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___78_1594.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___78_1594.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___78_1594.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___78_1594.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___78_1594.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___78_1594.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1624 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1624 with
        | (u,uu____1640,g_u) ->
            let uu____1654 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1654 (fun uu____1658  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1664 = FStar_Syntax_Util.un_squash t  in
    match uu____1664 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1668 =
          let uu____1669 = FStar_Syntax_Subst.compress t'  in
          uu____1669.FStar_Syntax_Syntax.n  in
        (match uu____1668 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1673 -> false)
    | uu____1674 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1682 = FStar_Syntax_Util.un_squash t  in
    match uu____1682 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1686 =
          let uu____1687 = FStar_Syntax_Subst.compress t'  in
          uu____1687.FStar_Syntax_Syntax.n  in
        (match uu____1686 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1691 -> false)
    | uu____1692 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1701  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : unit -> unit tac) =
  fun uu____1718  ->
    let uu____1721 =
      let uu____1724 = cur_goal ()  in
      bind uu____1724
        (fun g  ->
           (let uu____1731 =
              let uu____1736 =
                let uu____1737 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1737
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1736)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1731);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1721
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1748  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___79_1758 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___79_1758.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___79_1758.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___79_1758.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___79_1758.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___79_1758.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___79_1758.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___79_1758.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___79_1758.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___79_1758.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___79_1758.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1759 = set ps1  in
         bind uu____1759
           (fun uu____1764  ->
              let uu____1765 = FStar_BigInt.of_int_fs n1  in ret uu____1765))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1772  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1780 = FStar_BigInt.of_int_fs n1  in ret uu____1780)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1793  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1801 = FStar_BigInt.of_int_fs n1  in ret uu____1801)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1814  ->
    let uu____1817 = cur_goal ()  in
    bind uu____1817 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1849 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1849 phi  in
          let uu____1850 = new_uvar reason env typ  in
          bind uu____1850
            (fun u  ->
               let goal =
                 {
                   FStar_Tactics_Types.context = env;
                   FStar_Tactics_Types.witness = u;
                   FStar_Tactics_Types.goal_ty = typ;
                   FStar_Tactics_Types.opts = opts;
                   FStar_Tactics_Types.is_guard = false
                 }  in
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
             (fun uu____1899  ->
                let uu____1900 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1900)
             (fun uu____1902  ->
                try
                  let uu____1922 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1922
                with
                | FStar_Errors.Err (uu____1949,msg) ->
                    let uu____1951 = tts e t  in
                    let uu____1952 =
                      let uu____1953 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1953
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1951 uu____1952 msg
                | FStar_Errors.Error (uu____1960,msg,uu____1962) ->
                    let uu____1963 = tts e t  in
                    let uu____1964 =
                      let uu____1965 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1965
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1963 uu____1964 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac;
        FStar_TypeChecker_Normalize.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____1992  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___82_2010 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___82_2010.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___82_2010.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___82_2010.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___82_2010.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___82_2010.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___82_2010.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___82_2010.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___82_2010.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___82_2010.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___82_2010.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2034 = get_guard_policy ()  in
      bind uu____2034
        (fun old_pol  ->
           let uu____2040 = set_guard_policy pol  in
           bind uu____2040
             (fun uu____2044  ->
                bind t
                  (fun r  ->
                     let uu____2048 = set_guard_policy old_pol  in
                     bind uu____2048 (fun uu____2052  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2077 =
            let uu____2078 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2078.FStar_TypeChecker_Env.guard_f  in
          match uu____2077 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2082 = istrivial e f  in
              if uu____2082
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2090 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2090
                           (fun goal  ->
                              let goal1 =
                                let uu___83_2097 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___83_2097.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___83_2097.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___83_2097.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___83_2097.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2098 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2098
                           (fun goal  ->
                              let goal1 =
                                let uu___84_2105 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___84_2105.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___84_2105.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___84_2105.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___84_2105.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2113 =
                              let uu____2114 =
                                let uu____2115 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2115
                                 in
                              Prims.op_Negation uu____2114  in
                            if uu____2113
                            then
                              mlog
                                (fun uu____2120  ->
                                   let uu____2121 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2121)
                                (fun uu____2123  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2130 ->
                              mlog
                                (fun uu____2133  ->
                                   let uu____2134 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2134)
                                (fun uu____2136  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2146 =
      let uu____2149 = cur_goal ()  in
      bind uu____2149
        (fun goal  ->
           let uu____2155 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____2155
             (fun uu____2175  ->
                match uu____2175 with
                | (t1,typ,guard) ->
                    let uu____2187 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2187 (fun uu____2191  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2146
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2220 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2220 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2231  ->
    let uu____2234 = cur_goal ()  in
    bind uu____2234
      (fun goal  ->
         let uu____2240 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____2240
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2244 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____2244))
  
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
          let uu____2273 =
            let uu____2274 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2274.FStar_TypeChecker_Env.guard_f  in
          match uu____2273 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2282 = istrivial e f  in
              if uu____2282
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2290 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2290
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___87_2300 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___87_2300.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___87_2300.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___87_2300.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___87_2300.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2307  ->
    let uu____2310 = cur_goal ()  in
    bind uu____2310
      (fun g  ->
         let uu____2316 = is_irrelevant g  in
         if uu____2316
         then bind __dismiss (fun uu____2320  -> add_smt_goals [g])
         else
           (let uu____2322 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2322))
  
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
             let uu____2371 =
               try
                 let uu____2405 =
                   let uu____2414 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2414 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2405
               with | uu____2436 -> fail "divide: not enough goals"  in
             bind uu____2371
               (fun uu____2463  ->
                  match uu____2463 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___88_2489 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___88_2489.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___88_2489.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___88_2489.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___88_2489.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___88_2489.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___88_2489.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___88_2489.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___88_2489.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___88_2489.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___89_2491 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___89_2491.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___89_2491.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___89_2491.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___89_2491.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___89_2491.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___89_2491.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___89_2491.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___89_2491.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___89_2491.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2492 = set lp  in
                      bind uu____2492
                        (fun uu____2500  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2514 = set rp  in
                                     bind uu____2514
                                       (fun uu____2522  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___90_2538 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___90_2538.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___90_2538.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___90_2538.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___90_2538.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___90_2538.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___90_2538.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___90_2538.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___90_2538.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___90_2538.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2539 = set p'
                                                       in
                                                    bind uu____2539
                                                      (fun uu____2547  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2568 = divide FStar_BigInt.one f idtac  in
    bind uu____2568
      (fun uu____2581  -> match uu____2581 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2618::uu____2619 ->
             let uu____2622 =
               let uu____2631 = map tau  in
               divide FStar_BigInt.one tau uu____2631  in
             bind uu____2622
               (fun uu____2649  ->
                  match uu____2649 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2690 =
        bind t1
          (fun uu____2695  ->
             let uu____2696 = map t2  in
             bind uu____2696 (fun uu____2704  -> ret ()))
         in
      focus uu____2690
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2713  ->
    let uu____2716 =
      let uu____2719 = cur_goal ()  in
      bind uu____2719
        (fun goal  ->
           let uu____2728 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2728 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2743 =
                 let uu____2744 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2744  in
               if uu____2743
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2758 = new_uvar "intro" env' typ'  in
                  bind uu____2758
                    (fun u  ->
                       let uu____2764 =
                         let uu____2767 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2767  in
                       bind uu____2764
                         (fun bb  ->
                            if bb
                            then
                              let uu____2781 =
                                let uu____2784 =
                                  let uu___93_2785 = goal  in
                                  let uu____2786 = bnorm env' u  in
                                  let uu____2787 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2786;
                                    FStar_Tactics_Types.goal_ty = uu____2787;
                                    FStar_Tactics_Types.opts =
                                      (uu___93_2785.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___93_2785.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2784  in
                              bind uu____2781 (fun uu____2789  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2795 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2795)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2716
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2810  ->
    let uu____2817 = cur_goal ()  in
    bind uu____2817
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2834 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2834 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2853 =
                let uu____2854 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2854  in
              if uu____2853
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2874 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2874; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2892 =
                   let uu____2895 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2895  in
                 bind uu____2892
                   (fun u  ->
                      let lb =
                        let uu____2910 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2910 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2924 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2924 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2956 = trysolve goal tm  in
                          bind uu____2956
                            (fun bb  ->
                               if bb
                               then
                                 let uu____2972 =
                                   let uu____2975 =
                                     let uu___94_2976 = goal  in
                                     let uu____2977 = bnorm env' u  in
                                     let uu____2978 =
                                       let uu____2979 = comp_to_typ c  in
                                       bnorm env' uu____2979  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____2977;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____2978;
                                       FStar_Tactics_Types.opts =
                                         (uu___94_2976.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___94_2976.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____2975  in
                                 bind uu____2972
                                   (fun uu____2986  ->
                                      let uu____2987 =
                                        let uu____2992 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____2992, b)  in
                                      ret uu____2987)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____3006 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3006))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3024 = cur_goal ()  in
    bind uu____3024
      (fun goal  ->
         mlog
           (fun uu____3031  ->
              let uu____3032 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____3032)
           (fun uu____3037  ->
              let steps =
                let uu____3041 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3041
                 in
              let w =
                normalize steps goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.witness
                 in
              let t =
                normalize steps goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              replace_cur
                (let uu___95_3048 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___95_3048.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___95_3048.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___95_3048.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3072 =
          mlog
            (fun uu____3077  ->
               let uu____3078 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3078)
            (fun uu____3080  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3086 -> g.FStar_Tactics_Types.opts
                      | uu____3089 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3094  ->
                         let uu____3095 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3095)
                      (fun uu____3098  ->
                         let uu____3099 = __tc e t  in
                         bind uu____3099
                           (fun uu____3120  ->
                              match uu____3120 with
                              | (t1,uu____3130,uu____3131) ->
                                  let steps =
                                    let uu____3135 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3135
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3072
  
let (refine_intro : unit -> unit tac) =
  fun uu____3149  ->
    let uu____3152 =
      let uu____3155 = cur_goal ()  in
      bind uu____3155
        (fun g  ->
           let uu____3162 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____3162 with
           | (uu____3175,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___96_3200 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___96_3200.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___96_3200.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___96_3200.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___96_3200.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____3201 =
                 let uu____3206 =
                   let uu____3211 =
                     let uu____3212 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3212]  in
                   FStar_Syntax_Subst.open_term uu____3211 phi  in
                 match uu____3206 with
                 | (bvs,phi1) ->
                     let uu____3231 =
                       let uu____3232 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3232  in
                     (uu____3231, phi1)
                  in
               (match uu____3201 with
                | (bv1,phi1) ->
                    let uu____3245 =
                      let uu____3248 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____3248
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____3245
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3254  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3152
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3273 = cur_goal ()  in
      bind uu____3273
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____3282 = __tc env t  in
           bind uu____3282
             (fun uu____3301  ->
                match uu____3301 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3316  ->
                         let uu____3317 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____3318 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3317 uu____3318)
                      (fun uu____3321  ->
                         let uu____3322 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3322
                           (fun uu____3326  ->
                              mlog
                                (fun uu____3330  ->
                                   let uu____3331 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____3332 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3331 uu____3332)
                                (fun uu____3335  ->
                                   let uu____3336 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____3336
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3344 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____3345 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____3346 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____3347 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3344 uu____3345 uu____3346
                                             uu____3347)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3362 =
        mlog
          (fun uu____3367  ->
             let uu____3368 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3368)
          (fun uu____3371  ->
             let uu____3372 =
               let uu____3379 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3379  in
             bind uu____3372
               (fun uu___62_3388  ->
                  match uu___62_3388 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3397 =
                        let uu____3404 =
                          let uu____3407 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3407
                            (fun uu____3412  ->
                               let uu____3413 = refine_intro ()  in
                               bind uu____3413
                                 (fun uu____3417  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3404  in
                      bind uu____3397
                        (fun uu___61_3424  ->
                           match uu___61_3424 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3432 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3362
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3461 =
             let uu____3464 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3464  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3461
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
          let uu____3544 = f x  in
          bind uu____3544
            (fun y  ->
               let uu____3552 = mapM f xs  in
               bind uu____3552 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3572 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3592 = cur_goal ()  in
        bind uu____3592
          (fun goal  ->
             mlog
               (fun uu____3599  ->
                  let uu____3600 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3600)
               (fun uu____3603  ->
                  let uu____3604 =
                    let uu____3609 =
                      let uu____3612 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3612  in
                    trytac_exn uu____3609  in
                  bind uu____3604
                    (fun uu___63_3619  ->
                       match uu___63_3619 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3627  ->
                                let uu____3628 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3628)
                             (fun uu____3631  ->
                                let uu____3632 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3632 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3656  ->
                                         let uu____3657 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3657)
                                      (fun uu____3660  ->
                                         let uu____3661 =
                                           let uu____3662 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3662  in
                                         if uu____3661
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3666 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3666
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3692 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3692
                                                    in
                                                 let uu____3695 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3695
                                                   (fun uu____3708  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3710 =
                                                        let uu____3711 =
                                                          let uu____3714 =
                                                            let uu____3715 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3715
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3714
                                                           in
                                                        uu____3711.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3710 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          {
                                                            FStar_Syntax_Syntax.ctx_uvar_head
                                                              = uvar;
                                                            FStar_Syntax_Syntax.ctx_uvar_gamma
                                                              = uu____3739;
                                                            FStar_Syntax_Syntax.ctx_uvar_binders
                                                              = uu____3740;
                                                            FStar_Syntax_Syntax.ctx_uvar_typ
                                                              = uu____3741;
                                                            FStar_Syntax_Syntax.ctx_uvar_reason
                                                              = uu____3742;
                                                            FStar_Syntax_Syntax.ctx_uvar_should_check
                                                              = uu____3743;
                                                            FStar_Syntax_Syntax.ctx_uvar_range
                                                              = uu____3744;_}
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3768
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3768
                                                               then ret ()
                                                               else
                                                                 (let uu____3772
                                                                    =
                                                                    let uu____3775
                                                                    =
                                                                    let uu___97_3776
                                                                    = goal
                                                                     in
                                                                    let uu____3777
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3778
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___97_3776.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3777;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3778;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___97_3776.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3775]
                                                                     in
                                                                  add_goals
                                                                    uu____3772))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3833 =
        mlog
          (fun uu____3838  ->
             let uu____3839 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3839)
          (fun uu____3842  ->
             let uu____3843 = cur_goal ()  in
             bind uu____3843
               (fun goal  ->
                  let uu____3849 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3849
                    (fun uu____3871  ->
                       match uu____3871 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3884 =
                             let uu____3887 =
                               let uu____3890 = __apply uopt tm1 typ1  in
                               bind uu____3890
                                 (fun uu____3894  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3887  in
                           let uu____3895 =
                             let uu____3898 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3899 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3900 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3898 uu____3899 uu____3900
                              in
                           try_unif uu____3884 uu____3895)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3833
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3923 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3923
    then
      let uu____3930 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3945 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3986 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3930 with
      | (pre,post) ->
          let post1 =
            let uu____4016 =
              let uu____4025 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4025]  in
            FStar_Syntax_Util.mk_app post uu____4016  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4049 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4049
       then
         let uu____4056 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4056
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4079 =
      let uu____4082 =
        mlog
          (fun uu____4087  ->
             let uu____4088 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4088)
          (fun uu____4092  ->
             let is_unit_t t =
               let uu____4099 =
                 let uu____4100 = FStar_Syntax_Subst.compress t  in
                 uu____4100.FStar_Syntax_Syntax.n  in
               match uu____4099 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4104 -> false  in
             let uu____4105 = cur_goal ()  in
             bind uu____4105
               (fun goal  ->
                  let uu____4111 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____4111
                    (fun uu____4134  ->
                       match uu____4134 with
                       | (tm1,t,guard) ->
                           let uu____4146 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4146 with
                            | (bs,comp) ->
                                let uu____4173 = lemma_or_sq comp  in
                                (match uu____4173 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4192 =
                                       FStar_List.fold_left
                                         (fun uu____4238  ->
                                            fun uu____4239  ->
                                              match (uu____4238, uu____4239)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4342 =
                                                    is_unit_t b_t  in
                                                  if uu____4342
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4380 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____4380 with
                                                     | (u,uu____4410,g_u) ->
                                                         let uu____4424 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4424,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4192 with
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
                                          let uu____4497 =
                                            let uu____4500 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4500
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4497
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4508 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4509 =
                                                   let uu____4510 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4510
                                                    in
                                                 let uu____4511 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4508 uu____4509
                                                   uu____4511
                                               else
                                                 (let uu____4513 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4513
                                                    (fun uu____4518  ->
                                                       let uu____4519 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4519
                                                         (fun uu____4527  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4552
                                                                  =
                                                                  let uu____4555
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4555
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4552
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
                                                                   is_free_uvar
                                                                    uv
                                                                    g'.FStar_Tactics_Types.goal_ty)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4604
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4604
                                                              with
                                                              | (hd1,uu____4618)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    uv ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4636
                                                                    -> false)
                                                               in
                                                            let uu____4637 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4705
                                                                     ->
                                                                    match uu____4705
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range,uu____4730)
                                                                    ->
                                                                    let uu____4731
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4731
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4755)
                                                                    ->
                                                                    let env =
                                                                    let uu___100_4773
                                                                    =
                                                                    goal.FStar_Tactics_Types.context
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___100_4773.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let uu____4774
                                                                    =
                                                                    let uu____4775
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4775.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4774
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4788
                                                                    ->
                                                                    let uu____4789
                                                                    =
                                                                    let uu____4798
                                                                    =
                                                                    let uu____4801
                                                                    =
                                                                    let uu___101_4802
                                                                    = goal
                                                                     in
                                                                    let uu____4803
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4804
                                                                    =
                                                                    bnorm env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    = env;
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4803;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4804;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___101_4802.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___101_4802.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4801]
                                                                     in
                                                                    (uu____4798,
                                                                    [])  in
                                                                    ret
                                                                    uu____4789
                                                                    | 
                                                                    uu____4817
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4819
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4819
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
                                                                    let uu____4822
                                                                    =
                                                                    let uu____4829
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4829
                                                                    term1  in
                                                                    match uu____4822
                                                                    with
                                                                    | 
                                                                    (uu____4830,uu____4831,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4833
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4833
                                                                    (fun
                                                                    uu___64_4849
                                                                     ->
                                                                    match uu___64_4849
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
                                                            bind uu____4637
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4917
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4917
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4939
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4939
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5000
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5000
                                                                    then
                                                                    let uu____5003
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5003
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
                                                                    let uu____5017
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5017)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5018
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5018
                                                                   (fun
                                                                    uu____5023
                                                                     ->
                                                                    let uu____5024
                                                                    =
                                                                    let uu____5027
                                                                    =
                                                                    let uu____5028
                                                                    =
                                                                    let uu____5029
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____5029
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5028
                                                                     in
                                                                    if
                                                                    uu____5027
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5024
                                                                    (fun
                                                                    uu____5035
                                                                     ->
                                                                    let uu____5036
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5036
                                                                    (fun
                                                                    uu____5040
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4082  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4079
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5062 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5062 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5072::(e1,uu____5074)::(e2,uu____5076)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5119 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5143 = destruct_eq' typ  in
    match uu____5143 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5173 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5173 with
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
        let uu____5227 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5227 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5275 = aux e'  in
               FStar_Util.map_opt uu____5275
                 (fun uu____5299  ->
                    match uu____5299 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5320 = aux e  in
      FStar_Util.map_opt uu____5320
        (fun uu____5344  ->
           match uu____5344 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5411 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5411
            (fun uu____5435  ->
               match uu____5435 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___102_5454 = bv  in
                     let uu____5455 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___102_5454.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___102_5454.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5455
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___103_5464 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___103_5464.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___103_5464.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5474 = cur_goal ()  in
    bind uu____5474
      (fun goal  ->
         let uu____5482 = h  in
         match uu____5482 with
         | (bv,uu____5486) ->
             mlog
               (fun uu____5490  ->
                  let uu____5491 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5492 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5491
                    uu____5492)
               (fun uu____5495  ->
                  let uu____5496 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5496 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5525 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5525 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5540 =
                             let uu____5541 = FStar_Syntax_Subst.compress x
                                in
                             uu____5541.FStar_Syntax_Syntax.n  in
                           (match uu____5540 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___104_5558 = bv1  in
                                  let uu____5559 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___104_5558.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___104_5558.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5559
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5565 =
                                  let uu___105_5566 = goal  in
                                  let uu____5567 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5568 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5569 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5567;
                                    FStar_Tactics_Types.witness = uu____5568;
                                    FStar_Tactics_Types.goal_ty = uu____5569;
                                    FStar_Tactics_Types.opts =
                                      (uu___105_5566.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___105_5566.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5565
                            | uu____5570 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5571 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5592 = cur_goal ()  in
      bind uu____5592
        (fun goal  ->
           let uu____5603 = b  in
           match uu____5603 with
           | (bv,uu____5607) ->
               let bv' =
                 let uu____5609 =
                   let uu___106_5610 = bv  in
                   let uu____5611 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5611;
                     FStar_Syntax_Syntax.index =
                       (uu___106_5610.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___106_5610.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5609  in
               let s1 =
                 let uu____5615 =
                   let uu____5616 =
                     let uu____5623 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5623)  in
                   FStar_Syntax_Syntax.NT uu____5616  in
                 [uu____5615]  in
               let uu____5628 = subst_goal bv bv' s1 goal  in
               (match uu____5628 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5643 = cur_goal ()  in
    bind uu____5643
      (fun goal  ->
         let uu____5652 = b  in
         match uu____5652 with
         | (bv,uu____5656) ->
             let uu____5657 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5657 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5686 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5686 with
                   | (ty,u) ->
                       let uu____5695 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5695
                         (fun t'  ->
                            let bv'' =
                              let uu___107_5705 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___107_5705.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___107_5705.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5709 =
                                let uu____5710 =
                                  let uu____5717 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5717)  in
                                FStar_Syntax_Syntax.NT uu____5710  in
                              [uu____5709]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___108_5729 = b1  in
                                   let uu____5730 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___108_5729.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___108_5729.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5730
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5736  ->
                                 let uu____5737 =
                                   let uu____5740 =
                                     let uu____5743 =
                                       let uu___109_5744 = goal  in
                                       let uu____5745 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5746 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5745;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5746;
                                         FStar_Tactics_Types.opts =
                                           (uu___109_5744.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___109_5744.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5743]  in
                                   add_goals uu____5740  in
                                 bind uu____5737
                                   (fun uu____5749  ->
                                      let uu____5750 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5750
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5769 = cur_goal ()  in
      bind uu____5769
        (fun goal  ->
           let uu____5778 = b  in
           match uu____5778 with
           | (bv,uu____5782) ->
               let uu____5783 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5783 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5815 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5815
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___110_5820 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___110_5820.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___110_5820.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___111_5824 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___111_5824.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___111_5824.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___111_5824.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___111_5824.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : unit -> unit tac) =
  fun uu____5831  ->
    let uu____5834 = cur_goal ()  in
    bind uu____5834
      (fun goal  ->
         let uu____5840 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5840 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5862 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5862
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___112_5886 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___112_5886.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___112_5886.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5897 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5897
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5910 = cur_goal ()  in
    bind uu____5910
      (fun goal  ->
         mlog
           (fun uu____5918  ->
              let uu____5919 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5920 =
                let uu____5921 =
                  let uu____5922 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5922 FStar_List.length  in
                FStar_All.pipe_right uu____5921 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5919 uu____5920)
           (fun uu____5941  ->
              let uu____5942 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5942 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5989 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5989
                        then
                          let uu____5992 =
                            let uu____5993 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5993
                             in
                          fail uu____5992
                        else check1 bvs2
                     in
                  let uu____5995 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5995
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5999 = check1 bvs  in
                     bind uu____5999
                       (fun uu____6005  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6007 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____6007
                            (fun ut  ->
                               let uu____6013 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____6013
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___113_6022 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___113_6022.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___113_6022.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___113_6022.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6030  ->
    let uu____6033 = cur_goal ()  in
    bind uu____6033
      (fun goal  ->
         let uu____6039 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____6039 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6053) ->
             let uu____6058 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6058)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6068 = cur_goal ()  in
    bind uu____6068
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6078 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6078  in
         let g' =
           let uu___114_6080 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___114_6080.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___114_6080.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___114_6080.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___114_6080.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6082  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6092 = cur_goal ()  in
    bind uu____6092
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6102 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6102  in
         let g' =
           let uu___115_6104 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___115_6104.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___115_6104.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___115_6104.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___115_6104.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6106  -> add_goals [g']))
  
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
            let uu____6146 = FStar_Syntax_Subst.compress t  in
            uu____6146.FStar_Syntax_Syntax.n  in
          let uu____6149 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___119_6155 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___119_6155.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___119_6155.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6149
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6171 =
                   let uu____6172 = FStar_Syntax_Subst.compress t1  in
                   uu____6172.FStar_Syntax_Syntax.n  in
                 match uu____6171 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6199 = ff hd1  in
                     bind uu____6199
                       (fun hd2  ->
                          let fa uu____6221 =
                            match uu____6221 with
                            | (a,q) ->
                                let uu____6234 = ff a  in
                                bind uu____6234 (fun a1  -> ret (a1, q))
                             in
                          let uu____6247 = mapM fa args  in
                          bind uu____6247
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6313 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6313 with
                      | (bs1,t') ->
                          let uu____6322 =
                            let uu____6325 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6325 t'  in
                          bind uu____6322
                            (fun t''  ->
                               let uu____6329 =
                                 let uu____6330 =
                                   let uu____6347 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6354 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6347, uu____6354, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6330  in
                               ret uu____6329))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6423 = ff hd1  in
                     bind uu____6423
                       (fun hd2  ->
                          let ffb br =
                            let uu____6438 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6438 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6470 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6470  in
                                let uu____6471 = ff1 e  in
                                bind uu____6471
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6486 = mapM ffb brs  in
                          bind uu____6486
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6530;
                          FStar_Syntax_Syntax.lbtyp = uu____6531;
                          FStar_Syntax_Syntax.lbeff = uu____6532;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6534;
                          FStar_Syntax_Syntax.lbpos = uu____6535;_}::[]),e)
                     ->
                     let lb =
                       let uu____6560 =
                         let uu____6561 = FStar_Syntax_Subst.compress t1  in
                         uu____6561.FStar_Syntax_Syntax.n  in
                       match uu____6560 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6565) -> lb
                       | uu____6578 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6587 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6587
                         (fun def1  ->
                            ret
                              (let uu___116_6593 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___116_6593.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___116_6593.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___116_6593.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___116_6593.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___116_6593.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___116_6593.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6594 = fflb lb  in
                     bind uu____6594
                       (fun lb1  ->
                          let uu____6604 =
                            let uu____6609 =
                              let uu____6610 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6610]  in
                            FStar_Syntax_Subst.open_term uu____6609 e  in
                          match uu____6604 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6634 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6634  in
                              let uu____6635 = ff1 e1  in
                              bind uu____6635
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6676 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6676
                         (fun def  ->
                            ret
                              (let uu___117_6682 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___117_6682.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___117_6682.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___117_6682.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___117_6682.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___117_6682.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___117_6682.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6683 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6683 with
                      | (lbs1,e1) ->
                          let uu____6698 = mapM fflb lbs1  in
                          bind uu____6698
                            (fun lbs2  ->
                               let uu____6710 = ff e1  in
                               bind uu____6710
                                 (fun e2  ->
                                    let uu____6718 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6718 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6786 = ff t2  in
                     bind uu____6786
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6817 = ff t2  in
                     bind uu____6817
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6824 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___118_6831 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___118_6831.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___118_6831.FStar_Syntax_Syntax.vars)
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
            let uu____6868 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6868 with
            | (t1,lcomp,g) ->
                let uu____6880 =
                  (let uu____6883 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6883) ||
                    (let uu____6885 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6885)
                   in
                if uu____6880
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6895 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6895
                       (fun ut  ->
                          log ps
                            (fun uu____6906  ->
                               let uu____6907 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6908 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6907 uu____6908);
                          (let uu____6909 =
                             let uu____6912 =
                               let uu____6913 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6913 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6912 opts
                              in
                           bind uu____6909
                             (fun uu____6916  ->
                                let uu____6917 =
                                  bind tau
                                    (fun uu____6923  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6929  ->
                                            let uu____6930 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6931 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6930 uu____6931);
                                       ret ut1)
                                   in
                                focus uu____6917)))
                      in
                   let uu____6932 = trytac' rewrite_eq  in
                   bind uu____6932
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
          let uu____7130 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7130
            (fun t1  ->
               let uu____7138 =
                 f env
                   (let uu___122_7147 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___122_7147.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___122_7147.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7138
                 (fun uu____7163  ->
                    match uu____7163 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7186 =
                               let uu____7187 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7187.FStar_Syntax_Syntax.n  in
                             match uu____7186 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7220 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7220
                                   (fun uu____7245  ->
                                      match uu____7245 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7261 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7261
                                            (fun uu____7288  ->
                                               match uu____7288 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___120_7318 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___120_7318.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___120_7318.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7354 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7354 with
                                  | (bs1,t') ->
                                      let uu____7369 =
                                        let uu____7376 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7376 ctrl1 t'
                                         in
                                      bind uu____7369
                                        (fun uu____7394  ->
                                           match uu____7394 with
                                           | (t'',ctrl2) ->
                                               let uu____7409 =
                                                 let uu____7416 =
                                                   let uu___121_7419 = t4  in
                                                   let uu____7422 =
                                                     let uu____7423 =
                                                       let uu____7440 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7447 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7440,
                                                         uu____7447, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7423
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7422;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___121_7419.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___121_7419.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7416, ctrl2)  in
                                               ret uu____7409))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7494 -> ret (t3, ctrl1))))

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
              let uu____7537 = ctrl_tac_fold f env ctrl t  in
              bind uu____7537
                (fun uu____7561  ->
                   match uu____7561 with
                   | (t1,ctrl1) ->
                       let uu____7576 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____7576
                         (fun uu____7603  ->
                            match uu____7603 with
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
              let uu____7685 =
                let uu____7692 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7692
                  (fun uu____7701  ->
                     let uu____7702 = ctrl t1  in
                     bind uu____7702
                       (fun res  ->
                          let uu____7725 = trivial ()  in
                          bind uu____7725 (fun uu____7733  -> ret res)))
                 in
              bind uu____7685
                (fun uu____7749  ->
                   match uu____7749 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7773 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7773 with
                          | (t2,lcomp,g) ->
                              let uu____7789 =
                                (let uu____7792 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7792) ||
                                  (let uu____7794 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7794)
                                 in
                              if uu____7789
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7809 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7809
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7824  ->
                                           let uu____7825 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7826 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7825 uu____7826);
                                      (let uu____7827 =
                                         let uu____7830 =
                                           let uu____7831 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7831 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7830 opts
                                          in
                                       bind uu____7827
                                         (fun uu____7838  ->
                                            let uu____7839 =
                                              bind rewriter
                                                (fun uu____7853  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7859  ->
                                                        let uu____7860 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7861 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7860
                                                          uu____7861);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7839))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7909 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7909 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7946  ->
                     let uu____7947 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____7947);
                bind dismiss_all
                  (fun uu____7950  ->
                     let uu____7951 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7951
                       (fun uu____7969  ->
                          match uu____7969 with
                          | (gt',uu____7977) ->
                              (log ps
                                 (fun uu____7981  ->
                                    let uu____7982 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____7982);
                               (let uu____7983 = push_goals gs  in
                                bind uu____7983
                                  (fun uu____7987  ->
                                     add_goals
                                       [(let uu___123_7989 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___123_7989.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___123_7989.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___123_7989.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___123_7989.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____8015 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8015 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____8052  ->
                     let uu____8053 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____8053);
                bind dismiss_all
                  (fun uu____8056  ->
                     let uu____8057 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____8057
                       (fun gt'  ->
                          log ps
                            (fun uu____8067  ->
                               let uu____8068 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____8068);
                          (let uu____8069 = push_goals gs  in
                           bind uu____8069
                             (fun uu____8073  ->
                                add_goals
                                  [(let uu___124_8075 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___124_8075.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___124_8075.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___124_8075.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___124_8075.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : unit -> unit tac) =
  fun uu____8082  ->
    let uu____8085 = cur_goal ()  in
    bind uu____8085
      (fun g  ->
         let uu____8103 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____8103 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8109 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8109 with
              | (hd1,args) ->
                  let uu____8142 =
                    let uu____8153 =
                      let uu____8154 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8154.FStar_Syntax_Syntax.n  in
                    (uu____8153, args)  in
                  (match uu____8142 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8166::(l,uu____8168)::(r,uu____8170)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8197 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____8197
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8206 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____8207 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8206 uu____8207
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8210) ->
                       let uu____8223 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____8223))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8230  ->
    let uu____8233 = cur_goal ()  in
    bind uu____8233
      (fun g  ->
         let uu____8239 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____8239
           (fun u  ->
              let g' =
                let uu___125_8246 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___125_8246.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___125_8246.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___125_8246.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___125_8246.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____8249  ->
                   let uu____8250 =
                     let uu____8253 =
                       let uu____8254 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____8254
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____8253
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____8250
                     (fun uu____8257  ->
                        let uu____8258 = add_goals [g']  in
                        bind uu____8258 (fun uu____8262  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8269  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___126_8286 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___126_8286.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___126_8286.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___126_8286.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___126_8286.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___126_8286.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___126_8286.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___126_8286.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___126_8286.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___126_8286.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___126_8286.FStar_Tactics_Types.freshness)
                })
         | uu____8287 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8296  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___127_8309 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___127_8309.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___127_8309.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___127_8309.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___127_8309.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___127_8309.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___127_8309.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___127_8309.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___127_8309.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___127_8309.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___127_8309.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8316  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8323 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8343 =
      let uu____8350 = cur_goal ()  in
      bind uu____8350
        (fun g  ->
           let uu____8360 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____8360
             (fun uu____8396  ->
                match uu____8396 with
                | (t1,typ,guard) ->
                    let uu____8412 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8412 with
                     | (hd1,args) ->
                         let uu____8449 =
                           let uu____8462 =
                             let uu____8463 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8463.FStar_Syntax_Syntax.n  in
                           (uu____8462, args)  in
                         (match uu____8449 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8482)::(q,uu____8484)::[]) when
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
                                let uu___128_8522 = g  in
                                let uu____8523 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8523;
                                  FStar_Tactics_Types.witness =
                                    (uu___128_8522.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___128_8522.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___128_8522.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___128_8522.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___129_8525 = g  in
                                let uu____8526 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8526;
                                  FStar_Tactics_Types.witness =
                                    (uu___129_8525.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___129_8525.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___129_8525.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___129_8525.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____8533  ->
                                   let uu____8534 = add_goals [g1; g2]  in
                                   bind uu____8534
                                     (fun uu____8543  ->
                                        let uu____8544 =
                                          let uu____8549 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____8550 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____8549, uu____8550)  in
                                        ret uu____8544))
                          | uu____8555 ->
                              let uu____8568 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8568))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8343
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____8598 = cur_goal ()  in
    bind uu____8598
      (fun g  ->
         FStar_Options.push ();
         (let uu____8611 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____8611);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___130_8618 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___130_8618.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___130_8618.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___130_8618.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___130_8618.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____8626  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____8639  ->
    let uu____8642 = cur_goal ()  in
    bind uu____8642
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8655  ->
    let uu____8658 = cur_goal ()  in
    bind uu____8658
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8671  ->
    let uu____8674 = cur_goal ()  in
    bind uu____8674
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8695 =
        let uu____8698 = cur_goal ()  in
        bind uu____8698
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8706 = __tc env tm  in
             bind uu____8706
               (fun uu____8726  ->
                  match uu____8726 with
                  | (tm1,typ,guard) ->
                      let uu____8738 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8738 (fun uu____8742  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8695
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8765 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8771 =
              let uu____8772 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8772  in
            new_uvar "uvar_env.2" env uu____8771
         in
      bind uu____8765
        (fun typ  ->
           let uu____8784 = new_uvar "uvar_env" env typ  in
           bind uu____8784 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____8798 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8815 -> g.FStar_Tactics_Types.opts
             | uu____8818 -> FStar_Options.peek ()  in
           let uu____8821 = FStar_Syntax_Util.head_and_args t  in
           match uu____8821 with
           | ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar ctx_uvar;
                FStar_Syntax_Syntax.pos = uu____8837;
                FStar_Syntax_Syntax.vars = uu____8838;_},uu____8839)
               ->
               let env1 =
                 let uu___131_8859 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___131_8859.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___131_8859.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___131_8859.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___131_8859.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___131_8859.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___131_8859.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___131_8859.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___131_8859.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___131_8859.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___131_8859.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___131_8859.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___131_8859.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___131_8859.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___131_8859.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___131_8859.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___131_8859.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___131_8859.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___131_8859.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___131_8859.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___131_8859.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___131_8859.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___131_8859.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___131_8859.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___131_8859.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___131_8859.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___131_8859.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___131_8859.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___131_8859.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___131_8859.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___131_8859.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___131_8859.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___131_8859.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___131_8859.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___131_8859.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___131_8859.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___131_8859.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___131_8859.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let uu____8860 =
                 let uu____8863 =
                   let uu____8864 = bnorm env1 t  in
                   let uu____8865 =
                     bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
                   {
                     FStar_Tactics_Types.context = env1;
                     FStar_Tactics_Types.witness = uu____8864;
                     FStar_Tactics_Types.goal_ty = uu____8865;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8863]  in
               add_goals uu____8860
           | uu____8866 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8798
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  -> do_unify ps.FStar_Tactics_Types.main_context t1 t2)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____8921  ->
             let uu____8922 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8922
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8928  -> fun uu____8929  -> false)
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
        (fun uu____8947  ->
           let uu____8948 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8948)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____8958 =
      mlog
        (fun uu____8963  ->
           let uu____8964 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8964)
        (fun uu____8967  ->
           let uu____8968 = cur_goal ()  in
           bind uu____8968
             (fun g  ->
                let uu____8974 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8974
                  (fun uu____8994  ->
                     match uu____8994 with
                     | (ty1,uu____9004,guard) ->
                         let uu____9006 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____9006
                           (fun uu____9011  ->
                              let uu____9012 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____9012
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___132_9021 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___132_9021.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___132_9021.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___132_9021.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___132_9021.FStar_Tactics_Types.is_guard)
                                        })
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldUntil
                                          FStar_Syntax_Syntax.Delta_constant;
                                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                        FStar_TypeChecker_Normalize.Primops;
                                        FStar_TypeChecker_Normalize.Simplify;
                                        FStar_TypeChecker_Normalize.UnfoldTac;
                                        FStar_TypeChecker_Normalize.Unmeta]
                                         in
                                      let ng =
                                        normalize steps
                                          g.FStar_Tactics_Types.context
                                          g.FStar_Tactics_Types.goal_ty
                                         in
                                      let nty =
                                        normalize steps
                                          g.FStar_Tactics_Types.context ty1
                                         in
                                      let uu____9028 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____9028
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___133_9037 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___133_9037.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___133_9037.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___133_9037.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___133_9037.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8958
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9059::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9087 = init xs  in x :: uu____9087
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9104) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9161 = last args  in
        (match uu____9161 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9183 =
               let uu____9184 =
                 let uu____9189 =
                   let uu____9190 =
                     let uu____9195 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9195  in
                   uu____9190 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9189, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9184  in
             FStar_All.pipe_left ret uu____9183)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9206,uu____9207) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9251 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9251 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9284 =
                    let uu____9285 =
                      let uu____9290 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9290)  in
                    FStar_Reflection_Data.Tv_Abs uu____9285  in
                  FStar_All.pipe_left ret uu____9284))
    | FStar_Syntax_Syntax.Tm_type uu____9293 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9313 ->
        let uu____9326 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9326 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9356 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9356 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9395 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9403 =
          let uu____9404 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____9404  in
        FStar_All.pipe_left ret uu____9403
    | FStar_Syntax_Syntax.Tm_uvar ctx_u ->
        let uu____9408 =
          let uu____9409 =
            let uu____9418 =
              let uu____9419 =
                FStar_Syntax_Unionfind.uvar_id
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_BigInt.of_int_fs uu____9419  in
            (uu____9418, (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ))
             in
          FStar_Reflection_Data.Tv_Uvar uu____9409  in
        FStar_All.pipe_left ret uu____9408
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____9445 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____9450 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____9450 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____9489 ->
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
           | FStar_Util.Inr uu____9519 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____9523 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____9523 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____9543 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____9547 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9601 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9601
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9620 =
                let uu____9627 =
                  FStar_List.map
                    (fun uu____9639  ->
                       match uu____9639 with
                       | (p1,uu____9647) -> inspect_pat p1) ps
                   in
                (fv, uu____9627)  in
              FStar_Reflection_Data.Pat_Cons uu____9620
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
            (fun uu___65_9731  ->
               match uu___65_9731 with
               | (pat,uu____9749,t4) ->
                   let uu____9763 = inspect_pat pat  in (uu____9763, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9770 ->
        ((let uu____9772 =
            let uu____9777 =
              let uu____9778 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9779 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9778
                uu____9779
               in
            (FStar_Errors.Warning_CantInspect, uu____9777)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9772);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9792 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9792
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9796 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9796
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9800 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9800
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9807 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9807
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9826 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9826
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9839 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9839
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9854 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9854
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9858 =
          let uu____9859 =
            let uu____9866 =
              let uu____9867 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9867  in
            FStar_Syntax_Syntax.mk uu____9866  in
          uu____9859 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9858
    | FStar_Reflection_Data.Tv_Uvar (u,g,bs,t) ->
        let uu____9877 =
          let uu____9878 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9878 (g, bs, t)  in
        FStar_All.pipe_left ret uu____9877
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9897 =
          let uu____9898 =
            let uu____9905 =
              let uu____9906 =
                let uu____9919 =
                  let uu____9922 =
                    let uu____9923 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9923]  in
                  FStar_Syntax_Subst.close uu____9922 t2  in
                ((false, [lb]), uu____9919)  in
              FStar_Syntax_Syntax.Tm_let uu____9906  in
            FStar_Syntax_Syntax.mk uu____9905  in
          uu____9898 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9897
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9957 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____9957 with
         | (lbs,body) ->
             let uu____9972 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____9972)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10006 =
                let uu____10007 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10007  in
              FStar_All.pipe_left wrap uu____10006
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10014 =
                let uu____10015 =
                  let uu____10028 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10044 = pack_pat p1  in
                         (uu____10044, false)) ps
                     in
                  (fv, uu____10028)  in
                FStar_Syntax_Syntax.Pat_cons uu____10015  in
              FStar_All.pipe_left wrap uu____10014
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
            (fun uu___66_10090  ->
               match uu___66_10090 with
               | (pat,t1) ->
                   let uu____10107 = pack_pat pat  in
                   (uu____10107, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10155 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10155
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10183 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10183
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10229 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10229
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10268 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10268
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10289 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10289 with
      | (u,uu____10307,g_u) ->
          let g =
            let uu____10322 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____10322;
              FStar_Tactics_Types.is_guard = false
            }  in
          (g, g_u)
  
let (proofstate_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10337 = goal_of_goal_ty env typ  in
      match uu____10337 with
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
          (ps, (g.FStar_Tactics_Types.witness))
  